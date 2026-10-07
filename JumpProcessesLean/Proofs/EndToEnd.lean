import JumpProcessesLean.Proofs.DirectSimulationLaw
import JumpProcessesLean.Proofs.RSSASimulationLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- Input model conditions: a fixed finite channel set, total transitions, and
checked nonnegative enclosing bounds. No sampler law or output agreement is a
field of this structure. -/
structure ModelConsistency {σ : Type} {n : Nat} (model : Model ℝ σ)
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → ℝ) : Prop where
  nonnegative : ∀ x j, 0 ≤ rates x j
  bounds_valid : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j
  rates_eq : ∀ x, model.rates x = Array.ofFn (rates x)
  bounds_eq : ∀ x, model.bounds x = ⟨Array.ofFn (lower x), Array.ofFn (upper x)⟩
  transition_eq : ∀ x j, model.transition x j.val = .ok (transition x j)

noncomputable def targetSimulationLaw {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates : σ → Fin (n + 1) → ℝ) (initial : σ) (start horizon : ℝ)
    (fuel : Nat) (saveEvents : Bool) (observable : Except Error (TraceObservation ℝ σ) → X) : Measure X :=
  Measure.sum (fun word : Fin (fuel + 1) → Fin (n + 1) =>
    let marks := extendMarks word
    let states := stateAlongWord transition initial marks
    (targetWordLaw (fun l => completedRates (rates (states l))) marks (fuel + 1)).map
      (fun ts => observable (holdingSimulationObservation model states (fun l => rates (states l))
        marks start horizon fuel saveEvents ts)))

/-- Actual public `simulate` pushforwards, assembled from unnormalized primitive
reaction-word branches. RSSA uses its unbounded first-success stopping source,
with a finite transcript cap sufficient for that source. -/
noncomputable def nativeSimulationLaw {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper)
    (initial : σ) (start horizon : ℝ) (fuel : Nat) (saveEvents : Bool)
    (observable : Except Error (TraceObservation ℝ σ) → X) (algorithm : Algorithm) : Measure X :=
  Measure.sum (fun word : Fin (fuel + 1) → Fin (n + 1) =>
    let marks := extendMarks word
    let states := stateAlongWord transition initial marks
    let rr := fun l => rates (states l)
    let lo := fun l => lower (states l)
    let up := fun l => upper (states l)
    match algorithm with
    | .direct =>
      let P := directPacketSpecification model states rr marks
        (fun l => C.nonnegative (states l)) (fun l => C.rates_eq (states l))
      (rawWordLaw (fun l => directPacketInputs (rr l) (marks l)) (fuel + 1)).map
        (fun p => observable (packetCompiledRun P (1 / 2, 1 / 2) start horizon fuel saveEvents p))
    | .nrm =>
      (nrmRawPathLaw (fun l => completedRates (rr l)) marks (fuel + 1)).map
        (fun p => observable (nrmCompiledRun model states rr marks start horizon fuel 0 saveEvents p))
    | .rssa =>
      let P := rssaPacketSpecification model states rr lo up marks
        (fun l => C.bounds_valid (states l)) (fun l => C.rates_eq (states l))
        (fun l => C.bounds_eq (states l))
      (rawWordLaw (fun l => rssaPacketInputs (rr l) (lo l) (up l) (marks l)) (fuel + 1)).map
        (fun p => observable (packetCompiledRun P ⟨(0, 0), (fun _ => 1 / 2, fun _ => (1 / 2, 1 / 2))⟩
          start horizon fuel saveEvents p)))

/-- End-to-end theorem: independent primitive uniforms, actual native sampling
and persistent NRM updates, the public simulation loop, horizon/absorption
stopping, recording and event-budget errors all have the marked-exponential
path pushforward. -/
theorem native_simulation_law_eq_target {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper)
    (initial : σ) (start horizon : ℝ) (hstart : start < horizon)
    (fuel : Nat) (saveEvents : Bool) (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts => observable (holdingSimulationObservation model states
        (fun l => rates (states l)) marks start horizon fuel saveEvents ts))) (algorithm : Algorithm) :
    nativeSimulationLaw model transition rates lower upper C initial start horizon fuel saveEvents observable algorithm =
      targetSimulationLaw model transition rates initial start horizon fuel saveEvents observable := by
  unfold nativeSimulationLaw targetSimulationLaw
  congr 1
  funext word
  let marks := extendMarks word
  let states := stateAlongWord transition initial marks
  have hs : ∀ l, model.transition (states l) (marks l).val = .ok (states (l + 1)) := by
    intro l
    exact C.transition_eq (states l) (marks l)
  cases algorithm with
  | direct =>
    exact direct_simulation_word_law model states (fun l => rates (states l)) marks
      (fun l => C.nonnegative (states l)) (fun l => C.rates_eq (states l)) hs
      start horizon hstart fuel saveEvents observable (hobs word)
  | nrm =>
    exact nrm_simulation_word_law model states (fun l => rates (states l)) marks
      (fun l => C.nonnegative (states l)) (fun l => C.rates_eq (states l)) hs
      start horizon hstart fuel 0 saveEvents observable (hobs word)
  | rssa =>
    exact rssa_simulation_word_law model states (fun l => rates (states l))
      (fun l => lower (states l)) (fun l => upper (states l)) marks
      (fun l => C.bounds_valid (states l)) (fun l => C.rates_eq (states l))
      (fun l => C.bounds_eq (states l)) hs start horizon hstart fuel saveEvents observable (hobs word)

/-- Equality of the complete real Direct, NRM and unbounded RSSA simulation laws,
for every measurable observable of the stopped trace and error outcomes. -/
theorem direct_nrm_rssa_simulations_same_law {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper)
    (initial : σ) (start horizon : ℝ) (hstart : start < horizon)
    (fuel : Nat) (saveEvents : Bool) (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts => observable (holdingSimulationObservation model states
        (fun l => rates (states l)) marks start horizon fuel saveEvents ts))) (a b : Algorithm) :
    nativeSimulationLaw model transition rates lower upper C initial start horizon fuel saveEvents observable a =
      nativeSimulationLaw model transition rates lower upper C initial start horizon fuel saveEvents observable b := by
  rw [native_simulation_law_eq_target model transition rates lower upper C initial start horizon hstart
    fuel saveEvents observable hobs a,
    native_simulation_law_eq_target model transition rates lower upper C initial start horizon hstart
      fuel saveEvents observable hobs b]

/-- The derived common stopped simulation law has mass one. Primitive branch
measures are not normalized by hand or conditioned on eventual success. -/
theorem native_simulation_probability {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper)
    (initial : σ) (start horizon : ℝ) (hstart : start < horizon)
    (fuel : Nat) (saveEvents : Bool) (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts => observable (holdingSimulationObservation model states
        (fun l => rates (states l)) marks start horizon fuel saveEvents ts))) (algorithm : Algorithm) :
    IsProbabilityMeasure (nativeSimulationLaw model transition rates lower upper C initial start horizon
      fuel saveEvents observable algorithm) := by
  rw [native_simulation_law_eq_target model transition rates lower upper C initial start horizon hstart
    fuel saveEvents observable hobs algorithm]
  constructor
  unfold targetSimulationLaw
  rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  have hw (word : Fin (fuel + 1) → Fin (n + 1)) :
      ((targetWordLaw (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks word) l)))
          (extendMarks word) (fuel + 1)).map
        (fun ts => observable (holdingSimulationObservation model
          (stateAlongWord transition initial (extendMarks word))
          (fun l => rates (stateAlongWord transition initial (extendMarks word) l))
          (extendMarks word) start horizon fuel saveEvents ts))) univ =
      pathWordWeight transition rates initial word := by
    rw [Measure.map_apply (hobs word) MeasurableSet.univ, preimage_univ,
      target_word_mass _ (fun l => completedRates_positive_total _) _ _]
    unfold pathWordWeight
    apply Finset.prod_congr rfl
    intro q _
    congr 1
    simp only [extendMarks, q.isLt, dite_true]
  simp_rw [hw]
  exact path_word_weights_normalize transition rates C.nonnegative (fuel + 1) initial

end JumpProcessesLean.Proofs
