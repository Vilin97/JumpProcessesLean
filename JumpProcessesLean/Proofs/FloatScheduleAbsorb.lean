import JumpProcessesLean.Proofs.FloatIID

/-!
# Float schedules that may stop at an absorbing state

The trajectory composition used by every FloatLib refinement executes `fuel + 1`
scheduled events. Here the schedule may instead stop after `m ≤ fuel` events, when the
native sampler reports that no channel is active. The real replay then has the same
`m` events, so absorbing states are executed exactly rather than counted as failures.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- Native transcript of a schedule whose `m`th sampling call finds no active channel. -/
theorem scheduled_concrete_run_absorb {α σ R : Type} [Inhabited α] (op : Arithmetic α)
    (src : RandomSource α R) (model : Model α σ) (algorithm : Algorithm) (cap fuel m : Nat)
    (hm : m ≤ fuel) (states : Nat → σ) (times : Nat → α) (marks : Nat → Nat)
    (tape sampled : Nat → Nat → R) (cache : Nat → Option (NRMState α))
    (hstep : ∀ k count, k < m → k + count = fuel → sampleEvent op src model algorithm cap (states k)
      (times k) (tape k (count + 1)) (cache k) = .ok (some ⟨times (k + 1), marks k⟩, sampled k count))
    (habsorb : ∀ count, m + count = fuel → ∃ r, sampleEvent op src model algorithm cap (states m)
      (times m) (tape m (count + 1)) (cache m) = .ok (none, r))
    (htransition : ∀ k, k < m → model.transition (states k) (marks k) = .ok (states (k + 1)))
    (hupdate : ∀ k count, k < m → k + count + 1 = fuel → refreshCache op src model algorithm
      (states (k + 1)) ⟨times (k + 1), marks k⟩ (sampled k (count + 1)) (cache k) =
        .ok (cache (k + 1), tape (k + 1) (count + 1))) :
    ∀ d k r, k + d = m → k + r = fuel →
      ConcreteRun op src model algorithm cap r (states k) (times k) (tape k (r + 1)) (cache k)
        (scheduledEvents times marks k d) := by
  intro d
  induction d with
  | zero =>
    intro k r hk hr
    have hkm : k = m := by omega
    subst hkm
    obtain ⟨rng, hrng⟩ := habsorb r hr
    exact ConcreteRun.absorb hrng
  | succ d ih =>
    intro k r hk hr
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [scheduledEvents]
    exact ConcreteRun.next (hstep k (r' + 1) (by omega) (by omega)) (htransition k (by omega))
      (hupdate k r' (by omega) (by omega)) (ih (k + 1) r' (by omega) (by omega))

/-- Full float simulation approximation for a schedule ending at an absorbing state
after `m ≤ fuel` events. -/
theorem simulate_float_schedule_close_absorb {σ R : Type} (src : RandomSource Binary64 R)
    (mf : Model Binary64 σ) (mr : Model ℝ σ) (algorithm : Algorithm)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (tf : Nat → Binary64) (tr : Nat → ℝ) (marks : Nat → Nat)
    (hf : Binary64) (hr δ : ℝ) (fuel cap m : Nat) (hm : m ≤ fuel) (save : Bool)
    (tape sampled : Nat → Nat → R) (cache : Nat → Option (NRMState Binary64)) (initialTape : R)
    (hinit : initializeCache binary64Arithmetic src mf algorithm (states 0) (tf 0) initialTape =
      .ok (cache 0, tape 0 (fuel + 1)))
    (hvalid : (binary64Arithmetic.finite (tf 0) && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le (tf 0) hf) = true)
    (hstart : binary64Arithmetic.lt (tf 0) hf = true)
    (hhf : ExecFloat.Binary.isFinite hf = true)
    (hh : |floatReal hf - hr| ≤ δ) (h0 : |floatReal (tf 0) - tr 0| ≤ δ)
    (hstep : ∀ k count, k < m → k + count = fuel → sampleEvent binary64Arithmetic src mf algorithm cap
      (states k) (tf k) (tape k (count + 1)) (cache k) = .ok (some ⟨tf (k + 1), marks k⟩, sampled k count))
    (habsorb : ∀ count, m + count = fuel → ∃ r, sampleEvent binary64Arithmetic src mf algorithm cap
      (states m) (tf m) (tape m (count + 1)) (cache m) = .ok (none, r))
    (hstate : ∀ k, k < m → mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (hupdate : ∀ k count, k < m → k + count + 1 = fuel → refreshCache binary64Arithmetic src mf algorithm
      (states (k + 1)) ⟨tf (k + 1), marks k⟩ (sampled k (count + 1)) (cache k) =
        .ok (cache (k + 1), tape (k + 1) (count + 1)))
    (hfinite : ∀ k, k < m → ExecFloat.Binary.isFinite (tf (k + 1)) = true)
    (hinc : ∀ k, k < m → binary64Arithmetic.le (tf k) (tf (k + 1)) = true)
    (hrinc : ∀ k, k < m → tr k ≤ tr (k + 1))
    (herr : ∀ k, k < m → |floatReal (tf (k + 1)) - tr (k + 1)| ≤ δ)
    (hmargin : ∀ k, k < m → 2 * δ < |tr (k + 1) - hr|) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic src mf algorithm (states 0) (tf 0) hf initialTape fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) (tr 0) 0 #[(tr 0, states 0)]
        (scheduledEvents tr marks 0 m)) := by
  have hrun := scheduled_concrete_run_absorb binary64Arithmetic src mf algorithm cap fuel m hm states tf
    marks tape sampled cache hstep habsorb hstate hupdate m 0 fuel (by omega) (by omega)
  rw [simulate_float_refines_replay src mf algorithm (states 0) (tf 0) hf hvalid hstart initialTape
    (tape 0 (fuel + 1)) (cache 0) fuel cap save _ hinit hrun]
  cases m with
  | zero =>
    exact replay_float_trace_close mf mr htransition hf hr δ hhf hh save (tf 0) (tr 0) _ _
      (EventTapeClose.nil _ _) fuel (states 0) 0 _ _ (List.Forall₂.cons ⟨rfl, h0⟩ List.Forall₂.nil)
  | succ m =>
    exact replay_float_trace_close mf mr htransition hf hr δ hhf hh save (tf 0) (tr 0) _ _
      (scheduled_event_tapes_close tf tr marks hf hr δ m
        (fun k hk => hfinite k (by omega)) (fun k hk => hinc k (by omega))
        (fun k hk => hrinc k (by omega)) (fun k hk => herr k (by omega))
        (fun k hk => hmargin k (by omega)) 0 (m + 1) (by omega)) fuel (states 0) 0 _ _
      (List.Forall₂.cons ⟨rfl, h0⟩ List.Forall₂.nil)

/-- Whole native Direct/RSSA float composition stopping at an absorbing state after
`m ≤ fuel` events, with any unread tape suffix. -/
theorem float_packet_trajectory_close_absorb {σ γ : Type} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (algorithm : Algorithm) (hnrm : algorithm ≠ .nrm)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Nat)
    (clock : Nat → Binary64 → γ → Binary64) (u e : Nat → γ → List Binary64)
    (realClock : Nat → γ → ℝ) (source : Nat → γ) (tail : Tape Binary64)
    (start hf : Binary64) (sr hr ε d δ : ℝ) (fuel cap m : Nat) (hm : m ≤ fuel) (save : Bool)
    (hexec : ∀ k, k < m → ∀ us es,
      sampleEvent binary64Arithmetic (tapeSource Binary64) mf algorithm cap (states k)
        (floatTimeSchedule clock source start k)
        ⟨u k (source k) ++ us, e k (source k) ++ es⟩ none =
          .ok (some ⟨floatTimeSchedule clock source start (k + 1), marks k⟩, ⟨us, es⟩))
    (hfin : ∀ k, k < m → ExecFloat.Binary.isFinite (floatTimeSchedule clock source start (k + 1)) = true)
    (hinc : ∀ k, k < m → binary64Arithmetic.le (floatTimeSchedule clock source start k)
      (floatTimeSchedule clock source start (k + 1)) = true)
    (hpos : ∀ k, k < m → 0 ≤ realClock k (source k))
    (herrL : ∀ k, k < m → |floatReal (floatTimeSchedule clock source start (k + 1)) -
      (floatReal (floatTimeSchedule clock source start k) + realClock k (source k))| ≤ d)
    (habsorb : ∀ rng, sampleEvent binary64Arithmetic (tapeSource Binary64) mf algorithm cap (states m)
      (floatTimeSchedule clock source start m) rng none = .ok (none, rng))
    (hstate : ∀ k, k < m → mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true) (hstart : binary64Arithmetic.lt start hf = true)
    (hhf : ExecFloat.Binary.isFinite hf = true) (hh : |floatReal hf - hr| ≤ δ)
    (h0 : |floatReal start - sr| ≤ ε) (hd : 0 ≤ d)
    (hbudget : ε + ((fuel + 1 : Nat) : ℝ) * d ≤ δ)
    (hmargin : ∀ k, k < m → 2 * δ < |realTimeSchedule realClock source sr (k + 1) - hr|) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf algorithm (states 0) start hf
        (floatPacketTapeFrom u e source tail 0 (fuel + 1)) fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule realClock source sr) marks 0 m)) := by
  let tf := floatTimeSchedule clock source start
  let tr := realTimeSchedule realClock source sr
  let tape := floatPacketTapeFrom u e source tail
  have hacc : ∀ k, k ≤ m → |floatReal (tf k) - tr k| ≤ ε + (k : ℝ) * d := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa only [tf, tr, floatTimeSchedule, realTimeSchedule, Nat.cast_zero, zero_mul, add_zero] using h0
    | succ k ih =>
      intro hk
      have h := absolute_time_error _ _ _ _ (ε + (k : ℝ) * d) d (ih (by omega)) (herrL k (by omega))
      simpa only [tf, tr, realTimeSchedule, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using h
  have hbound (k : Nat) (hk : k ≤ fuel + 1) : ε + (k : ℝ) * d ≤ δ := by
    have hcast : (k : ℝ) ≤ ((fuel + 1 : Nat) : ℝ) := by exact_mod_cast hk
    exact (add_le_add (le_refl ε) (mul_le_mul_of_nonneg_right hcast hd)).trans hbudget
  apply simulate_float_schedule_close_absorb (tapeSource Binary64) mf mr algorithm htransition states tf tr
    marks hf hr δ fuel cap m hm save tape (fun k count => tape (k + 1) count) (fun _ => none)
    (tape 0 (fuel + 1))
  · cases algorithm with
    | direct => rfl
    | rssa => rfl
    | nrm => exact (hnrm rfl).elim
  · exact hvalid
  · exact hstart
  · exact hhf
  · exact hh
  · exact h0.trans (by simpa only [Nat.cast_zero, zero_mul, add_zero] using hbound 0 (by omega))
  · intro k count hk _
    change sampleEvent _ _ _ _ _ _ _ (floatPacketTapeFrom u e source tail k (count + 1)) _ = _
    rw [floatPacketTapeFrom]
    exact hexec k hk _ _
  · intro count _
    exact ⟨_, habsorb _⟩
  · exact hstate
  · intro k count hk _
    cases algorithm <;> rfl
  · exact hfin
  · exact hinc
  · intro k hk
    change tr k ≤ tr k + realClock k (source k)
    exact le_add_of_nonneg_right (hpos k hk)
  · intro k hk
    exact (hacc (k + 1) (by omega)).trans (hbound (k + 1) (by omega))
  · exact hmargin

/-- Stopped replays coincide with the schedule up to the first absorbing state. -/
lemma scheduled_events_eq_nrm_absorb {n : Nat} (rates c : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (times : Nat → ℝ) (m : Nat)
    (hA : ∀ l, l < m → 0 < ∑ j, rates l j) (hZ : ¬0 < ∑ j, rates m j) :
    ∀ fuel k, k ≤ m → m ≤ k + fuel →
      scheduledEvents times (fun l => (marks l).val) k (m - k) =
        nrmScheduleEvents rates c marks times k fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk hkm
    have hkm' : k = m := by omega
    subst hkm'
    rw [nrmScheduleEvents, if_neg hZ, Nat.sub_self]
    rfl
  | succ fuel ih =>
    intro k hk hkm
    by_cases hkeq : k = m
    · subst hkeq
      rw [nrmScheduleEvents, if_neg hZ, Nat.sub_self]
      rfl
    · have hlt : k < m := by omega
      rw [nrmScheduleEvents, if_pos (hA k hlt), show m - k = (m - (k + 1)) + 1 by omega, scheduledEvents,
        ih (k + 1) (by omega) (by omega)]

end JumpProcessesLean.Proofs
