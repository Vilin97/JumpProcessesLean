import JumpProcessesLean.Proofs.FullFloatLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set

/-- Includes transition/event-limit errors, or the terminal state and jump count. -/
def discreteTraceOutcome {α σ : Type} : Except Error (TraceObservation α σ) → Except Error (σ × Nat)
  | .error e => .error e
  | .ok t => .ok (t.state, t.events)

noncomputable def realListTimestamp {σ : Type} : List (ℝ × σ) → Nat → ℝ
  | [], _ => 0
  | p :: _, 0 => p.1
  | _ :: rest, k + 1 => realListTimestamp rest k

noncomputable def floatListTimestamp {σ : Type} : List (Binary64 × σ) → Nat → ℝ
  | [], _ => 0
  | p :: _, 0 => floatReal p.1
  | _ :: rest, k + 1 => floatListTimestamp rest k

noncomputable def realRecordedTimestamp {σ : Type} (k : Nat) : Except Error (TraceObservation ℝ σ) → ℝ
  | .error _ => 0
  | .ok t => realListTimestamp t.trace.toList k

noncomputable def floatRecordedTimestamp {σ : Type} (k : Nat) : Except Error (TraceObservation Binary64 σ) → ℝ
  | .error _ => 0
  | .ok t => floatListTimestamp t.trace.toList k

lemma trace_list_timestamp_error {σ : Type} (δ : ℝ) (hδ : 0 ≤ δ)
    (fs : List (Binary64 × σ)) (rs : List (ℝ × σ))
    (h : List.Forall₂ (TraceEntryClose δ) fs rs) (k : Nat) :
    |floatListTimestamp fs k - realListTimestamp rs k| ≤ δ := by
  induction h generalizing k with
  | nil => simp [floatListTimestamp, realListTimestamp, hδ]
  | @cons f r fs rs he ht ih =>
    cases k with
    | zero => exact he.2
    | succ k => exact ih k

/-- Concrete observables for the complete distribution theorem: every saved
clock has the timestamp budget, and terminal state/count/error outcomes agree. -/
theorem recorded_trace_observables_close {σ : Type} (δ : ℝ) (hδ : 0 ≤ δ) (k : Nat)
    (f : Except Error (TraceObservation Binary64 σ)) (r : Except Error (TraceObservation ℝ σ))
    (h : TraceClose δ f r) :
    |floatRecordedTimestamp k f - realRecordedTimestamp k r| ≤ δ ∧
      discreteTraceOutcome f = discreteTraceOutcome r := by
  cases f with
  | error e =>
    cases r with
    | error e' =>
      change e = e' at h
      subst e'
      exact ⟨by simp [floatRecordedTimestamp, realRecordedTimestamp, hδ], rfl⟩
    | ok t => exact False.elim h
  | ok tf =>
    cases r with
    | error e => exact False.elim h
    | ok tr =>
      obtain ⟨hs, he, hh, ht⟩ := h
      exact ⟨trace_list_timestamp_error δ hδ tf.trace.toList tr.trace.toList ht k,
        by simp only [discreteTraceOutcome, hs, he]⟩

end JumpProcessesLean.Proofs
