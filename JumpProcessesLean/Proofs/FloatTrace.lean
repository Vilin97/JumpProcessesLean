import JumpProcessesLean.Proofs.EndToEnd
import JumpProcessesLean.Proofs.NRMFloatPropagation
import Mathlib.Data.List.Forall2

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

def TraceEntryClose {σ : Type} (δ : ℝ) (f : Binary64 × σ) (r : ℝ × σ) : Prop :=
  f.2 = r.2 ∧ |floatReal f.1 - r.1| ≤ δ

def TraceClose {σ : Type} (δ : ℝ) :
    Except Error (TraceObservation Binary64 σ) → Except Error (TraceObservation ℝ σ) → Prop
  | .error a, .error b => a = b
  | .ok f, .ok r => f.state = r.state ∧ f.events = r.events ∧
      |floatReal f.time - r.time| ≤ δ ∧
      List.Forall₂ (TraceEntryClose δ) f.trace.toList r.trace.toList
  | _, _ => False

/-- Clock input margins for deterministic replay. Native call agreement is
supplied later by the proved algorithm-specific arithmetic refinements. -/
inductive EventTapeClose (δ : ℝ) (hf : Binary64) (hr : ℝ) :
    Binary64 → ℝ → List (Event Binary64) → List (Event ℝ) → Prop
  | nil (nf nr) : EventTapeClose δ hf hr nf nr [] []
  | cons {nf nr ef er fs rs}
      (reaction : ef.reaction = er.reaction)
      (finite : ExecFloat.Binary.isFinite ef.time = true)
      (floatIncreasing : binary64Arithmetic.le nf ef.time = true)
      (realIncreasing : nr ≤ er.time)
      (error : |floatReal ef.time - er.time| ≤ δ)
      (horizonMargin : 2 * δ < |er.time - hr|)
      (tail : EventTapeClose δ hf hr ef.time er.time fs rs) :
      EventTapeClose δ hf hr nf nr (ef :: fs) (er :: rs)

lemma trace_close_push {σ : Type} (δ : ℝ) (tf : Array (Binary64 × σ)) (tr : Array (ℝ × σ))
    (h : List.Forall₂ (TraceEntryClose δ) tf.toList tr.toList) (f : Binary64 × σ) (r : ℝ × σ)
    (he : TraceEntryClose δ f r) :
    List.Forall₂ (TraceEntryClose δ) (tf.push f).toList (tr.push r).toList := by
  simp only [Array.toList_push]
  exact List.rel_append h (List.Forall₂.cons he List.Forall₂.nil)

/-- Complete replay approximation: terminal state/count, every recorded state,
all timestamps and event-limit/transition errors are covered. -/
theorem replay_float_trace_close {σ : Type} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (hf : Binary64) (hr δ : ℝ) (hhf : ExecFloat.Binary.isFinite hf = true)
    (hh : |floatReal hf - hr| ≤ δ) (save : Bool)
    (nf : Binary64) (nr : ℝ) (fs : List (Event Binary64)) (rs : List (Event ℝ))
    (he : EventTapeClose δ hf hr nf nr fs rs) (fuel : Nat) (state : σ) (count : Nat)
    (tf : Array (Binary64 × σ)) (tr : Array (ℝ × σ))
    (ht : List.Forall₂ (TraceEntryClose δ) tf.toList tr.toList) :
    TraceClose δ (replayEvents binary64Arithmetic mf hf save fuel state nf count tf fs)
      (replayEvents realArithmetic mr hr save fuel state nr count tr rs) := by
  induction he generalizing fuel state count tf tr with
  | nil nf nr =>
    simp only [replayEvents, TraceClose]
    exact ⟨trivial, trivial, hh, trace_close_push δ tf tr ht (hf, state) (hr, state) ⟨rfl, hh⟩⟩
  | @cons nf nr ef er fs rs hrx hfin hinc hrinc herr hgap htail ih =>
    have hcmp : binary64Arithmetic.le ef.time hf = realArithmetic.le er.time hr := by
      change decide (ef.time ≤ hf) = decide (er.time ≤ hr)
      exact decide_eq_decide.mpr ((float_le_real ef.time hf hfin hhf).trans
        (rejection_margin_stable er.time hr (floatReal ef.time) (floatReal hf) δ herr hh hgap))
    have hvalid : (!binary64Arithmetic.le nf ef.time || !binary64Arithmetic.finite ef.time) = false := by
      simp only [hinc, show binary64Arithmetic.finite ef.time = true from hfin, Bool.not_true, Bool.or_self]
    have hrvalid : (!realArithmetic.le nr er.time || !realArithmetic.finite er.time) = false := by
      simp [realArithmetic, hrinc]
    rw [replayEvents.eq_def, replayEvents.eq_def]
    simp only [hvalid, hrvalid, Bool.false_eq_true, ite_false, hcmp]
    by_cases hstop : er.time ≤ hr
    · simp only [realArithmetic, hstop, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      cases fuel with
      | zero => rfl
      | succ fuel =>
        rw [hrx, htransition]
        cases hs : mr.transition state er.reaction with
        | error e => simp [hs, Bind.bind, Except.bind, TraceClose]
        | ok next =>
          simp only [hs, Bind.bind, Except.bind]
          apply ih fuel next (count + 1)
          cases save with
          | false => exact ht
          | true => exact trace_close_push δ tf tr ht (ef.time, next) (er.time, next) ⟨rfl, herr⟩
    · simp only [realArithmetic, hstop, decide_false, Bool.not_false, ite_true, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, hh, trace_close_push δ tf tr ht (hf, state) (hr, state) ⟨rfl, hh⟩⟩

/-- The public FloatLib wrapper refines replay with its actual initialization. -/
theorem simulate_float_refines_replay {σ R : Type} (src : RandomSource Binary64 R)
    (model : Model Binary64 σ) (algorithm : Algorithm) (initial : σ) (start horizon : Binary64)
    (hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite horizon &&
      binary64Arithmetic.le start horizon) = true)
    (hstart : binary64Arithmetic.lt start horizon = true)
    (rng initializedRng : R) (cache : Option (NRMState Binary64))
    (maxEvents maxProposals : Nat) (saveEvents : Bool) (events : List (Event Binary64))
    (hinit : initializeCache binary64Arithmetic src model algorithm initial start rng =
      .ok (cache, initializedRng))
    (hrun : ConcreteRun binary64Arithmetic src model algorithm maxProposals
      maxEvents initial start initializedRng cache events) :
    observeRun (simulate binary64Arithmetic src model algorithm initial start horizon rng
      maxEvents saveEvents maxProposals) =
      replayEvents binary64Arithmetic model horizon saveEvents maxEvents initial start 0 #[(start, initial)] events := by
  unfold simulate
  simp only [hvalid, hstart, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hinit]
  simp only [Bind.bind, Except.bind]
  exact simulateLoop_refines_replay _ _ _ _ _ _ _ _ _ _ _ _ _ hrun _ _

/-- A trace approximation gives joint tail envelopes for any observable which is
Lipschitz with respect to timestamp error and any mark constant on close traces. -/
theorem coupled_trace_observable_bounds {Ω σ ι : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : Ω → Except Error (TraceObservation ℝ σ))
    (F : Ω → Except Error (TraceObservation Binary64 σ))
    (T : Except Error (TraceObservation ℝ σ) → ℝ)
    (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι)
    (If : Except Error (TraceObservation Binary64 σ) → ι)
    (bad : Set Ω) (hbad : MeasurableSet bad) (δ ε : ℝ) (hε : 0 ≤ ε)
    (htrace : ∀ p ∉ bad, TraceClose δ (F p) (R p))
    (hobservable : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ ε ∧ If f = I r)
    (i : ι) (t : ℝ) :
    μ {p | t + ε < T (R p) ∧ I (R p) = i} ≤ μ {p | t < Tf (F p) ∧ If (F p) = i} + μ bad ∧
      μ {p | t < Tf (F p) ∧ If (F p) = i} ≤ μ {p | t - ε < T (R p) ∧ I (R p) = i} + μ bad := by
  exact coupled_joint_tail_bounds μ (fun p => T (R p)) (fun p => Tf (F p))
    (fun p => I (R p)) (fun p => If (F p)) bad hbad ε hε
    (fun p hp => hobservable (F p) (R p) (htrace p hp)) i t

end JumpProcessesLean.Proofs
