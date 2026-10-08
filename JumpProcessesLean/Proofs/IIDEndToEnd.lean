import JumpProcessesLean.Proofs.FloatIID

/-!
# End-to-end theorems on IID random input

Headline statements for the public `simulate` driver run on two independent IID
Uniform(0,1) streams (uniform draws and the uniforms behind `-log` exponential draws):

* Direct and NRM have exactly the target stopped-trajectory law, hence the same law.
* Fixed-cap RSSA is within the explicit proposal-cap defect of that law, and its
  event probabilities converge to the target as the cap grows.
* The common law is a probability measure and equals the native word-branch law.

The FloatLib approximation theorems are in `FloatIIDStop.lean`, with absorbing states
and inactive NRM channels. `FloatEndToEnd.lean` compares the FloatLib Direct and NRM
simulators with the real simulators on the same streams.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal BigOperators Topology

/-- The public Direct and NRM simulators on IID streams have one common law: the target
stopped-trajectory law, which is also the native law of every algorithm. -/
theorem iid_direct_nrm_same_law {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper)
    (initial : σ) (start horizon : ℝ) (hstart : start < horizon)
    (fuel capD capN : Nat) (saveEvents : Bool) (a b : Nat) (ha : fuel + 1 ≤ a)
    (hb : (n + 1) * (fuel + 1) ≤ b)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts => observable (holdingSimulationObservation model states
        (fun l => rates (states l)) marks start horizon fuel saveEvents ts)))
    (alg : Algorithm) :
    let direct := iidStreams.map (fun ω => observable (observeRun (simulate realArithmetic
      (tapeSource ℝ) model .direct initial start horizon (streamTape a b ω) fuel saveEvents capD)))
    let nrm := iidStreams.map (fun ω => observable (observeRun (simulate realArithmetic
      (tapeSource ℝ) model .nrm initial start horizon (streamTape a b ω) fuel saveEvents capN)))
    direct = nrm ∧
      direct = targetSimulationLaw model transition rates initial start horizon fuel saveEvents observable ∧
      direct = nativeSimulationLaw model transition rates lower upper C initial start horizon fuel
        saveEvents observable alg ∧
      IsProbabilityMeasure direct := by
  intro direct nrm
  have hfb : fuel + 1 ≤ b := le_trans (by nlinarith) hb
  have hd : direct = targetSimulationLaw model transition rates initial start horizon fuel saveEvents
      observable :=
    direct_iid_simulation_law model transition rates lower upper C initial start horizon hstart fuel capD
      saveEvents a b ha hfb observable hobs
  have hn : nrm = targetSimulationLaw model transition rates initial start horizon fuel saveEvents
      observable :=
    nrm_iid_simulation_law model transition rates lower upper C initial start horizon hstart fuel capN
      saveEvents a b hb observable hobs
  have hnative := native_simulation_law_eq_target model transition rates lower upper C initial start
    horizon hstart fuel saveEvents observable hobs alg
  have hprob := native_simulation_probability model transition rates lower upper C initial start horizon
    hstart fuel saveEvents observable hobs alg
  refine ⟨hd.trans hn.symm, hd, hd.trans hnative.symm, ?_⟩
  rw [hd, ← hnative]
  exact hprob

/-- Event probabilities of the public fixed-cap RSSA simulator on IID streams converge to
the exact target law as the proposal cap grows (with tapes long enough for the cap). -/
theorem iid_rssa_tendsto_target {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper)
    (initial : σ) (start horizon : ℝ) (hstart : start < horizon)
    (fuel : Nat) (saveEvents : Bool) (a b : ℕ → ℕ)
    (ha : ∀ N, 2 * N * (fuel + 1) ≤ a N) (hb : ∀ N, N * (fuel + 1) ≤ b N)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts => observable (holdingSimulationObservation model states
        (fun l => rates (states l)) marks start horizon fuel saveEvents ts)))
    (S : Set X) (hS : MeasurableSet S) :
    Tendsto (fun N => iidStreams ((fun ω => observable (observeRun (simulate realArithmetic
        (tapeSource ℝ) model .rssa initial start horizon (streamTape (a N) (b N) ω) fuel saveEvents N)))
          ⁻¹' S))
      atTop (𝓝 (targetSimulationLaw model transition rates initial start horizon fuel saveEvents
        observable S)) := by
  let target := targetSimulationLaw model transition rates initial start horizon fuel saveEvents observable
  let δ := fun N => rssaCapDefect transition rates lower upper C.bounds_valid initial fuel N
  have hδ : Tendsto δ atTop (𝓝 0) :=
    rssaCapDefect_tendsto_zero transition rates lower upper C.bounds_valid initial fuel
  have hbounds := fun N => (rssa_iid_capped_simulation_law model transition rates lower upper C initial
    start horizon hstart fuel N saveEvents (a N) (b N) (ha N) (hb N) observable hobs).2.2 S hS
  have hfinite : target S ≠ ∞ := by
    have hprob := (iid_direct_nrm_same_law model transition rates lower upper C initial start horizon
      hstart fuel 0 0 saveEvents (fuel + 1) ((n + 1) * (fuel + 1)) le_rfl le_rfl observable hobs
      .direct).2.2.2
    rw [(iid_direct_nrm_same_law model transition rates lower upper C initial start horizon
      hstart fuel 0 0 saveEvents (fuel + 1) ((n + 1) * (fuel + 1)) le_rfl le_rfl observable hobs
      .direct).2.1] at hprob
    exact measure_ne_top _ _
  have hlow : Tendsto (fun N => target S - δ N) atTop (𝓝 (target S)) := by
    have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := target S)) hδ (Or.inl hfinite)
    simpa only [tsub_zero] using h
  have hhigh : Tendsto (fun N => target S + δ N) atTop (𝓝 (target S)) := by
    have h := (tendsto_const_nhds (x := target S)).add hδ
    simpa only [add_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hhigh (fun N => ?_) (fun N => (hbounds N).2)
  exact tsub_le_iff_right.mpr (hbounds N).1

end JumpProcessesLean.Proofs
