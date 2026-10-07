import JumpProcessesLean.Proofs.DirectFloatStep

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

def scheduledEvents {α : Type} (times : Nat → α) (marks : Nat → Nat) : Nat → Nat → List (Event α)
  | _, 0 => []
  | k, count + 1 => ⟨times (k + 1), marks k⟩ :: scheduledEvents times marks (k + 1) count

/-- A generic driver lemma; each algorithm below discharges these local native
calls from input arithmetic certificates. -/
theorem scheduled_concrete_run {α σ R : Type} [Inhabited α] (op : Arithmetic α)
    (src : RandomSource α R) (model : Model α σ) (algorithm : Algorithm) (cap limit : Nat)
    (states : Nat → σ) (times : Nat → α) (marks : Nat → Nat)
    (tape sampled : Nat → Nat → R) (cache : Nat → Option (NRMState α))
    (hstep : ∀ k count, k + count ≤ limit → sampleEvent op src model algorithm cap (states k)
      (times k) (tape k (count + 1)) (cache k) =
        .ok (some ⟨times (k + 1), marks k⟩, sampled k count))
    (htransition : ∀ k, model.transition (states k) (marks k) = .ok (states (k + 1)))
    (hupdate : ∀ k count, k + count + 1 ≤ limit → refreshCache op src model algorithm (states (k + 1))
      ⟨times (k + 1), marks k⟩ (sampled k (count + 1)) (cache k) =
        .ok (cache (k + 1), tape (k + 1) (count + 1)))
    (k fuel : Nat) (hlen : k + fuel ≤ limit) :
    ConcreteRun op src model algorithm cap fuel (states k) (times k) (tape k (fuel + 1)) (cache k)
      (scheduledEvents times marks k (fuel + 1)) := by
  induction fuel generalizing k with
  | zero => exact ConcreteRun.budget (hstep k 0 (by omega))
  | succ fuel ih =>
    rw [scheduledEvents]
    exact ConcreteRun.next (hstep k (fuel + 1) (by omega)) (htransition k)
      (hupdate k fuel (by omega)) (ih (k + 1) (by omega))

theorem scheduled_event_tapes_close (tf : Nat → Binary64) (tr : Nat → ℝ) (marks : Nat → Nat)
    (hf : Binary64) (hr δ : ℝ) (limit : Nat)
    (hfinite : ∀ k, k ≤ limit → ExecFloat.Binary.isFinite (tf (k + 1)) = true)
    (hinc : ∀ k, k ≤ limit → binary64Arithmetic.le (tf k) (tf (k + 1)) = true)
    (hrinc : ∀ k, k ≤ limit → tr k ≤ tr (k + 1))
    (herr : ∀ k, k ≤ limit → |floatReal (tf (k + 1)) - tr (k + 1)| ≤ δ)
    (hmargin : ∀ k, k ≤ limit → 2 * δ < |tr (k + 1) - hr|)
    (k count : Nat) (hlen : k + count ≤ limit + 1) :
    EventTapeClose δ hf hr (tf k) (tr k)
      (scheduledEvents tf marks k count) (scheduledEvents tr marks k count) := by
  induction count generalizing k with
  | zero => exact EventTapeClose.nil _ _
  | succ count ih =>
    exact EventTapeClose.cons rfl (hfinite k (by omega)) (hinc k (by omega))
      (hrinc k (by omega)) (herr k (by omega)) (hmargin k (by omega)) (ih (k + 1) (by omega))

/-- Full float simulation approximation for a numerically certified native
schedule. This is an internal composition theorem; the public algorithm
instances derive every call premise from primitive-input certificates. -/
theorem simulate_float_schedule_close {σ R : Type} (src : RandomSource Binary64 R)
    (mf : Model Binary64 σ) (mr : Model ℝ σ) (algorithm : Algorithm)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (tf : Nat → Binary64) (tr : Nat → ℝ) (marks : Nat → Nat)
    (hf : Binary64) (hr δ : ℝ) (fuel cap : Nat) (save : Bool)
    (tape sampled : Nat → Nat → R) (cache : Nat → Option (NRMState Binary64)) (initialTape : R)
    (hinit : initializeCache binary64Arithmetic src mf algorithm (states 0) (tf 0) initialTape =
      .ok (cache 0, tape 0 (fuel + 1)))
    (hvalid : (binary64Arithmetic.finite (tf 0) && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le (tf 0) hf) = true)
    (hstart : binary64Arithmetic.lt (tf 0) hf = true)
    (hhf : ExecFloat.Binary.isFinite hf = true)
    (hh : |floatReal hf - hr| ≤ δ) (h0 : |floatReal (tf 0) - tr 0| ≤ δ)
    (hstep : ∀ k count, k + count ≤ fuel → sampleEvent binary64Arithmetic src mf algorithm cap (states k)
      (tf k) (tape k (count + 1)) (cache k) = .ok (some ⟨tf (k + 1), marks k⟩, sampled k count))
    (hstate : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (hupdate : ∀ k count, k + count + 1 ≤ fuel → refreshCache binary64Arithmetic src mf algorithm
      (states (k + 1)) ⟨tf (k + 1), marks k⟩ (sampled k (count + 1)) (cache k) =
        .ok (cache (k + 1), tape (k + 1) (count + 1)))
    (hfinite : ∀ k, k ≤ fuel → ExecFloat.Binary.isFinite (tf (k + 1)) = true)
    (hinc : ∀ k, k ≤ fuel → binary64Arithmetic.le (tf k) (tf (k + 1)) = true)
    (hrinc : ∀ k, k ≤ fuel → tr k ≤ tr (k + 1))
    (herr : ∀ k, k ≤ fuel → |floatReal (tf (k + 1)) - tr (k + 1)| ≤ δ)
    (hmargin : ∀ k, k ≤ fuel → 2 * δ < |tr (k + 1) - hr|) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic src mf algorithm (states 0) (tf 0) hf initialTape fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) (tr 0) 0 #[(tr 0, states 0)]
        (scheduledEvents tr marks 0 (fuel + 1))) := by
  have hrun := scheduled_concrete_run binary64Arithmetic src mf algorithm cap fuel states tf marks
    tape sampled cache hstep hstate hupdate 0 fuel (by omega)
  rw [simulate_float_refines_replay src mf algorithm (states 0) (tf 0) hf hvalid hstart initialTape
    (tape 0 (fuel + 1)) (cache 0) fuel cap save _ hinit hrun]
  exact replay_float_trace_close mf mr htransition hf hr δ hhf hh save (tf 0) (tr 0) _ _
    (scheduled_event_tapes_close tf tr marks hf hr δ fuel hfinite hinc hrinc herr hmargin 0 (fuel + 1)
      (by omega)) fuel (states 0) 0 _ _ (List.Forall₂.cons ⟨rfl, h0⟩ List.Forall₂.nil)

end JumpProcessesLean.Proofs
