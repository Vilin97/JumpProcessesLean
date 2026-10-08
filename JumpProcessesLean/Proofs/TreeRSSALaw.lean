import JumpProcessesLean.Proofs.TreeRSSACorrect
import JumpProcessesLean.Proofs.IIDEndToEnd

/-!
# The law of Tree-RSSA on IID streams

Tree-RSSA reads the same two IID Uniform(0,1) streams as the public driver. By
`treeRSSA_simulate_eq` it is the native capped RSSA on the bracket model, so:

* with proposal cap `N`, every event probability is within the explicit cap defect `δ_N`
  of the target stopped-trajectory law (`tree_rssa_iid_capped_law`);
* as `N → ∞`, every event probability converges to the probability of the same event
  under the public Direct simulator, i.e. Gillespie's exact SSA on the same streams
  (`tree_rssa_tendsto_direct`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal BigOperators Topology

variable {X : Type} [MeasurableSpace X] {n : Nat}

/-- Tree-RSSA with proposal cap `N` is within the cap defect of the target law. -/
theorem tree_rssa_iid_capped_law (net : Network ℝ) (hM : net.reactions.size = n + 1)
    (hv : ValidNetwork net) (initial : State) (hb : Bracketed net initial) (start horizon : ℝ)
    (hstart : start < horizon) (fuel N : Nat) (save : Bool) (a b : Nat)
    (ha : 2 * N * (fuel + 1) ≤ a) (hbN : N * (fuel + 1) ≤ b)
    (observable : Except Error (TraceObservation ℝ State) → X)
    (hobs : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord (bracketTransition net) initial marks
      Measurable (fun ts => observable (holdingSimulationObservation (bracketModel net) states
        (fun l => bracketRates net hM (states l)) marks start horizon fuel save ts))) :
    let F := fun ω => observable (observeRun (TreeRSSA.simulate realArithmetic (tapeSource ℝ) net
      initial start horizon (streamTape a b ω) fuel save N))
    let target := targetSimulationLaw (bracketModel net) (bracketTransition net) (bracketRates net hM)
      initial start horizon fuel save observable
    let δ := rssaCapDefect (bracketTransition net) (bracketRates net hM) (bracketLower net hM)
      (bracketUpper net hM) (bracketModel_consistency net hM hv).bounds_valid initial fuel N
    ∀ S, MeasurableSet S → target S ≤ iidStreams (F ⁻¹' S) + δ ∧
      iidStreams (F ⁻¹' S) ≤ target S + δ := by
  intro F target δ S hS
  have hF : F = fun ω => observable (observeRun (JumpProcessesLean.simulate realArithmetic
      (tapeSource ℝ) (bracketModel net) .rssa initial start horizon (streamTape a b ω) fuel save N)) := by
    funext ω
    simp only [F]
    rw [treeRSSA_simulate_eq net hv (tapeSource ℝ) initial hb]
  rw [hF]
  exact (rssa_iid_capped_simulation_law (bracketModel net) _ _ _ _ (bracketModel_consistency net hM hv)
    initial start horizon hstart fuel N save a b ha hbN observable hobs).2.2 S hS

/-- As the proposal cap grows, Tree-RSSA's event probabilities converge to those of the
public Direct simulator (Gillespie's exact SSA) run on the same IID streams. -/
theorem tree_rssa_tendsto_direct (net : Network ℝ) (hM : net.reactions.size = n + 1)
    (hv : ValidNetwork net) (initial : State) (hb : Bracketed net initial) (start horizon : ℝ)
    (hstart : start < horizon) (fuel : Nat) (save : Bool) (a b : ℕ → ℕ)
    (ha : ∀ N, 2 * N * (fuel + 1) ≤ a N) (hbN : ∀ N, N * (fuel + 1) ≤ b N)
    (observable : Except Error (TraceObservation ℝ State) → X)
    (hobs : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord (bracketTransition net) initial marks
      Measurable (fun ts => observable (holdingSimulationObservation (bracketModel net) states
        (fun l => bracketRates net hM (states l)) marks start horizon fuel save ts)))
    (S : Set X) (hS : MeasurableSet S) :
    Tendsto (fun N => iidStreams ((fun ω => observable (observeRun (TreeRSSA.simulate realArithmetic
        (tapeSource ℝ) net initial start horizon (streamTape (a N) (b N) ω) fuel save N))) ⁻¹' S))
      atTop (𝓝 (iidStreams.map (fun ω => observable (observeRun (JumpProcessesLean.simulate
        realArithmetic (tapeSource ℝ) (bracketModel net) .direct initial start horizon
          (streamTape (fuel + 1) ((n + 1) * (fuel + 1)) ω) fuel save 0))) S)) := by
  have hC := bracketModel_consistency net hM hv
  have hsame := iid_direct_nrm_same_law (bracketModel net) (bracketTransition net) (bracketRates net hM)
    (bracketLower net hM) (bracketUpper net hM) hC initial start horizon hstart fuel 0 0 save (fuel + 1)
    ((n + 1) * (fuel + 1)) le_rfl le_rfl observable hobs .direct
  rw [hsame.2.1]
  have hconv := iid_rssa_tendsto_target (bracketModel net) (bracketTransition net) (bracketRates net hM)
    (bracketLower net hM) (bracketUpper net hM) hC initial start horizon hstart fuel save a b ha hbN
    observable hobs S hS
  refine hconv.congr (fun N => ?_)
  congr 1
  ext ω
  simp only [mem_preimage]
  rw [treeRSSA_simulate_eq net hv (tapeSource ℝ) initial hb]

end JumpProcessesLean.Proofs
