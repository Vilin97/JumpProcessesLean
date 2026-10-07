import JumpProcessesLean.Proofs.DriverRefinement

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- A probability completion at absorbing states. Virtual events are discarded by
the observation before reaching the concrete driver; they do not revive the model. -/
noncomputable def completedRates {n : Nat} (rates : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  if 0 < ∑ j, rates j then rates else fun j => if j = 0 then 1 else 0

lemma completedRates_nonnegative {n : Nat} (rates : Fin (n + 1) → ℝ)
    (hr : ∀ j, 0 ≤ rates j) : ∀ j, 0 ≤ completedRates rates j := by
  intro j; unfold completedRates
  split_ifs <;> first | exact hr j | positivity

lemma completedRates_positive_total {n : Nat} (rates : Fin (n + 1) → ℝ) :
    0 < ∑ j, completedRates rates j := by
  unfold completedRates
  split_ifs with h
  · exact h
  · simp

noncomputable def completedLower {n : Nat} (rates lower : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  if 0 < ∑ j, rates j then lower else fun _ => 0

noncomputable def completedUpper {n : Nat} (rates upper : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  if 0 < ∑ j, rates j then upper else fun j => if j = 0 then 1 else 0

lemma completedBounds_valid {n : Nat} (rates lower upper : Fin (n + 1) → ℝ)
    (hb : ∀ j, 0 ≤ lower j ∧ lower j ≤ rates j ∧ rates j ≤ upper j) :
    ∀ j, 0 ≤ completedLower rates lower j ∧ completedLower rates lower j ≤ completedRates rates j ∧
      completedRates rates j ≤ completedUpper rates upper j := by
  intro j
  by_cases h : 0 < ∑ j, rates j
  · simpa only [completedLower, completedRates, completedUpper, h, ite_true] using hb j
  · by_cases hj : j = 0 <;> simp [completedLower, completedRates, completedUpper, h, hj]

def extendMarks {n k : Nat} (word : Fin k → Fin (n + 1)) (l : Nat) : Fin (n + 1) :=
  if h : l < k then word ⟨l, h⟩ else 0

noncomputable def eventWordMeasure {n : Nat} (algorithm : Algorithm)
    (rates lower upper : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1)) (k : Nat) :
    Measure (Fin k → ℝ) :=
  match algorithm with
  | .direct => directWordLaw rates marks k
  | .nrm => (maskedCachedWordLaw rates marks k).map Prod.fst
  | .rssa => rssaWordLaw rates lower upper marks k

theorem event_word_measure_law {n : Nat} (algorithm : Algorithm)
    (rates lower upper : Nat → Fin (n + 1) → ℝ) (hr : ∀ l j, 0 ≤ rates l j)
    (hA : ∀ l, 0 < ∑ j, rates l j)
    (hb : ∀ l j, 0 ≤ lower l j ∧ lower l j ≤ rates l j ∧ rates l j ≤ upper l j)
    (marks : Nat → Fin (n + 1)) (k : Nat) :
    eventWordMeasure algorithm rates lower upper marks k = targetWordLaw rates marks k := by
  cases algorithm with
  | direct => exact direct_nonnegative_word_law rates hr hA marks k
  | nrm => exact masked_cached_word_marginal rates hr marks k
  | rssa => exact rssa_nonnegative_word_law rates lower upper hA hb marks k

abbrev FinitePath (n k : Nat) := (Fin k → Fin (n + 1)) × (Fin k → ℝ)

/-- Complete finite path measure, summing every reaction word. Its NRM component
iterates the actual cached update; its RSSA component sums actual successful branches. -/
noncomputable def operationalFinitePathLaw {σ : Type} {n : Nat} (algorithm : Algorithm)
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → ℝ)
    (initial : σ) (k : Nat) : Measure (FinitePath n k) :=
  Measure.sum (fun word : Fin k → Fin (n + 1) =>
    let marks := extendMarks word
    let states := stateAlongWord transition initial marks
    (eventWordMeasure algorithm (fun l => completedRates (rates (states l)))
      (fun l => completedLower (rates (states l)) (lower (states l)))
      (fun l => completedUpper (rates (states l)) (upper (states l))) marks k).map
        (fun ts => (word, ts)))

/-- Equality of complete finite state-dependent path measures. Absorbing states are
included through unused probability completions, which the trace observation stops. -/
theorem operational_finite_paths_same_law {σ : Type} {n : Nat}
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → ℝ)
    (hr : ∀ x j, 0 ≤ rates x j)
    (hb : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j)
    (initial : σ) (k : Nat) (a b : Algorithm) :
    operationalFinitePathLaw a transition rates lower upper initial k =
      operationalFinitePathLaw b transition rates lower upper initial k := by
  unfold operationalFinitePathLaw
  congr 1
  funext word
  dsimp only
  have hl (algorithm : Algorithm) := event_word_measure_law algorithm
    (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks word) l)))
    (fun l => completedLower (rates (stateAlongWord transition initial (extendMarks word) l))
      (lower (stateAlongWord transition initial (extendMarks word) l)))
    (fun l => completedUpper (rates (stateAlongWord transition initial (extendMarks word) l))
      (upper (stateAlongWord transition initial (extendMarks word) l)))
    (fun l => completedRates_nonnegative _ (hr _))
    (fun l => completedRates_positive_total _)
    (fun l => completedBounds_valid _ _ _ (hb _)) (extendMarks word) k
  rw [hl a, hl b]

noncomputable def eventsFromPath {n k : Nat} (start : ℝ) (p : FinitePath n k) : List (Event ℝ) :=
  List.ofFn (fun j : Fin k =>
    ⟨start + ∑ q : Fin k, if q.val ≤ j.val then p.2 ⟨k - 1 - q.val, by omega⟩ else 0,
      (p.1 j).val⟩)

/-- Stops before a virtual event at an absorbing state. Transition errors are left
for replay to report, exactly as in the concrete driver. -/
noncomputable def stopAtAbsorption {σ : Type} {n : Nat}
    (rates : σ → Fin (n + 1) → ℝ) (transition : σ → Fin (n + 1) → σ) :
    σ → List (Event ℝ) → List (Event ℝ)
  | _, [] => []
  | state, e :: rest =>
    if 0 < ∑ j, rates state j then
      if h : e.reaction < n + 1 then
        e :: stopAtAbsorption rates transition (transition state ⟨e.reaction, h⟩) rest
      else [e]
    else []

noncomputable def finiteSimulationObservation {σ : Type} {n : Nat}
    (model : Model ℝ σ) (rates : σ → Fin (n + 1) → ℝ)
    (transition : σ → Fin (n + 1) → σ) (initial : σ) (start horizon : ℝ)
    (maxEvents : Nat) (saveEvents : Bool) (p : FinitePath n (maxEvents + 1)) :
    Except Error (TraceObservation ℝ σ) :=
  replayEvents realArithmetic model horizon saveEvents maxEvents initial start 0 #[(start, initial)]
    (stopAtAbsorption rates transition initial (eventsFromPath start p))

/-- End-to-end equality for every Borel observable of the full finite-horizon trace,
including terminal state, recording choices, absorbing stopping and event limits.
The concrete driver is connected to this observation by `simulate_refines_replay`. -/
theorem finite_simulation_observables_same_law {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ) (hr : ∀ x j, 0 ≤ rates x j)
    (hb : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j)
    (initial : σ) (start horizon : ℝ) (maxEvents : Nat) (saveEvents : Bool)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hm : Measurable (fun p => observable (finiteSimulationObservation model rates transition initial
      start horizon maxEvents saveEvents p))) (a b : Algorithm) :
    (operationalFinitePathLaw a transition rates lower upper initial (maxEvents + 1)).map
      (fun p => observable (finiteSimulationObservation model rates transition initial start horizon maxEvents saveEvents p)) =
    (operationalFinitePathLaw b transition rates lower upper initial (maxEvents + 1)).map
      (fun p => observable (finiteSimulationObservation model rates transition initial start horizon maxEvents saveEvents p)) := by
  rw [operational_finite_paths_same_law transition rates lower upper hr hb initial (maxEvents + 1) a b]

end JumpProcessesLean.Proofs
