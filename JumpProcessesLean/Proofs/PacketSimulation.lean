import JumpProcessesLean.Proofs.IndependentRawPath

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- Primitive packet specification for samplers without a persistent cache. Its
execution fields are instantiated below by proved Direct/RSSA tape refinements. -/
structure PacketSpecification {σ γ : Type} {n : Nat} (model : Model ℝ σ) (algorithm : Algorithm)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1)) where
  clock : Nat → γ → ℝ
  uniforms : Nat → γ → List ℝ
  exponentials : Nat → γ → List ℝ
  cost : Nat → γ → Nat
  good : Nat → γ → Prop
  uncached : algorithm ≠ .nrm
  execute : ∀ k p, good k p → 0 < ∑ j, rates k j → ∀ cap, cost k p ≤ cap →
    ∀ now us es, sampleEvent realArithmetic (tapeSource ℝ) model algorithm cap (states k) now
      ⟨uniforms k p ++ us, exponentials k p ++ es⟩ none =
      .ok (some ⟨now + clock k p, (marks k).val⟩, ⟨us, es⟩)
  absorb : ∀ k, ¬0 < ∑ j, rates k j → ∀ cap now rng,
    sampleEvent realArithmetic (tapeSource ℝ) model algorithm cap (states k) now rng none =
      .ok (none, rng)

def packetTape {γ : Type} (uniforms exponentials : Nat → γ → List ℝ)
    (source : Nat → γ) : Nat → Nat → Tape ℝ
  | _, 0 => ⟨[], []⟩
  | k, count + 1 =>
    let next := packetTape uniforms exponentials source (k + 1) count
    ⟨uniforms k (source k) ++ next.uniforms, exponentials k (source k) ++ next.exponentials⟩

theorem packet_schedule_concrete_run {σ γ : Type} {n : Nat} (model : Model ℝ σ) (algorithm : Algorithm)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (P : PacketSpecification (γ := γ) model algorithm states rates marks)
    (source : Nat → γ) (start : ℝ) (limit cap : Nat)
    (hg : ∀ k, k ≤ limit → P.good k (source k))
    (hcost : ∀ k, k ≤ limit → P.cost k (source k) ≤ cap)
    (hs : ∀ k, model.transition (states k) (marks k).val = .ok (states (k + 1)))
    (k fuel : Nat) (hlen : k + fuel ≤ limit) :
    let c := fun l (_ : Fin (n + 1)) => P.clock l (source l)
    let times := nrmScheduleTime c marks start
    ConcreteRun realArithmetic (tapeSource ℝ) model algorithm cap fuel (states k) (times k)
      (packetTape P.uniforms P.exponentials source k (fuel + 1)) none
      (nrmScheduleEvents rates c marks times k fuel) := by
  dsimp only
  let c := fun l (_ : Fin (n + 1)) => P.clock l (source l)
  let times := nrmScheduleTime c marks start
  induction fuel generalizing k with
  | zero =>
    rw [nrmScheduleEvents]
    by_cases hA : 0 < ∑ j, rates k j
    · rw [if_pos hA]
      apply ConcreteRun.budget
      rw [packetTape]
      exact P.execute k (source k) (hg k (by omega)) hA cap (hcost k (by omega)) (times k) _ _
    · rw [if_neg hA]
      apply ConcreteRun.absorb
      exact P.absorb k hA cap (times k) _
  | succ fuel ih =>
    rw [nrmScheduleEvents]
    by_cases hA : 0 < ∑ j, rates k j
    · rw [if_pos hA]
      apply ConcreteRun.next
        (newState := states (k + 1)) (newCache := none)
        (newRng := packetTape P.uniforms P.exponentials source (k + 1) (fuel + 1))
      · rw [packetTape]
        exact P.execute k (source k) (hg k (by omega)) hA cap (hcost k (by omega)) (times k) _ _
      · exact hs k
      · cases algorithm <;> try rfl
      · exact ih (k + 1) (by omega)
    · rw [if_neg hA]
      apply ConcreteRun.absorb
      exact P.absorb k hA cap (times k) _

noncomputable def packetCap {σ γ : Type} {n : Nat} {model : Model ℝ σ} {algorithm : Algorithm}
    {states : Nat → σ} {rates : Nat → Fin (n + 1) → ℝ} {marks : Nat → Fin (n + 1)}
    (P : PacketSpecification (γ := γ) model algorithm states rates marks)
    (source : Nat → γ) (fuel : Nat) : Nat :=
  ∑ q : Fin (fuel + 1), P.cost q.val (source q.val)

noncomputable def packetCompiledRun {σ γ : Type} {n : Nat} {model : Model ℝ σ} {algorithm : Algorithm}
    {states : Nat → σ} {rates : Nat → Fin (n + 1) → ℝ} {marks : Nat → Fin (n + 1)}
    (P : PacketSpecification (γ := γ) model algorithm states rates marks)
    (fallback : γ) (start horizon : ℝ) (fuel : Nat) (saveEvents : Bool)
    (p : Fin (fuel + 1) → γ) : Except Error (TraceObservation ℝ σ) :=
  let source := rawChronological fallback p
  observeRun (simulate realArithmetic (tapeSource ℝ) model algorithm (states 0) start horizon
    (packetTape P.uniforms P.exponentials source 0 (fuel + 1)) fuel saveEvents (packetCap P source fuel))

/-- Full native driver refinement from the actual finite packet source. RSSA
uses a cap large enough for the finite first-success transcript; this realizes
the unbounded first-success semantics without silently conditioning on success. -/
theorem packet_raw_driver_executes {σ γ : Type} [MeasurableSpace γ] {n : Nat}
    (model : Model ℝ σ) (algorithm : Algorithm)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (P : PacketSpecification (γ := γ) model algorithm states rates marks)
    (inputs : Nat → Measure γ) (hf : ∀ k, IsFiniteMeasure (inputs k))
    (hm : ∀ k, MeasurableSet {p | P.good k p})
    (hg : ∀ k, ∀ᵐ p ∂inputs k, P.good k p) (fallback : γ)
    (hs : ∀ k, model.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start horizon : ℝ) (hstart : start < horizon) (fuel : Nat) (saveEvents : Bool) :
    ∀ᵐ p ∂rawWordLaw inputs (fuel + 1),
      packetCompiledRun P fallback start horizon fuel saveEvents p =
        holdingSimulationObservation model states rates marks start horizon fuel saveEvents
          (rawWordHoldings P.clock (fuel + 1) p) := by
  filter_upwards [raw_word_good_ae inputs hf P.good hm hg (fuel + 1)] with p hp
  let source := rawChronological fallback p
  let c := fun l (_ : Fin (n + 1)) => P.clock l (source l)
  let times := nrmScheduleTime c marks start
  have hcost : ∀ k, k ≤ fuel → P.cost k (source k) ≤ packetCap P source fuel := by
    intro k hk
    change P.cost k (source k) ≤ ∑ q : Fin (fuel + 1), P.cost q.val (source q.val)
    exact Finset.single_le_sum (f := fun q : Fin (fuel + 1) => P.cost q.val (source q.val))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨k, by omega⟩ : Fin (fuel + 1)))
  have hrun := packet_schedule_concrete_run model algorithm states rates marks P source start fuel _
    (fun k hk => raw_chronological_good fallback p P.good hp k (by omega)) hcost hs 0 fuel (by omega)
  have he := simulate_refines_replay (tapeSource ℝ) model algorithm (states 0) start horizon hstart
    (packetTape P.uniforms P.exponentials source 0 (fuel + 1))
    (packetTape P.uniforms P.exponentials source 0 (fuel + 1)) none fuel _ saveEvents _
    (by cases algorithm with
        | direct => rfl
        | rssa => rfl
        | nrm => exact (P.uncached rfl).elim) hrun
  unfold packetCompiledRun
  rw [he]
  unfold holdingSimulationObservation
  have htimes : ∀ l, l ≤ fuel + 1 →
      times l = nrmScheduleTime (holdingSchedule (rawWordHoldings P.clock (fuel + 1) p)) marks start l := by
    intro l hl
    induction l with
    | zero => rfl
    | succ l ih =>
      change times l + P.clock l (source l) = _
      rw [nrmScheduleTime, ih (by omega), raw_chronological_clock fallback p P.clock l (by omega) (marks l)]
  rw [schedule_events_times_congr rates c _ marks _ _ (fuel + 1) htimes 0 fuel (by omega)]

theorem packet_simulation_word_law {σ γ X : Type} [MeasurableSpace γ] [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (algorithm : Algorithm)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (P : PacketSpecification (γ := γ) model algorithm states rates marks)
    (inputs : Nat → Measure γ) (hf : ∀ k, IsFiniteMeasure (inputs k))
    (hgoodM : ∀ k, MeasurableSet {p | P.good k p})
    (hgood : ∀ k, ∀ᵐ p ∂inputs k, P.good k p)
    (hclock : ∀ k, Measurable (P.clock k))
    (hlaw : ∀ k, (inputs k).map (P.clock k) =
      ENNReal.ofReal (completedRates (rates k) (marks k) / (∑ j, completedRates (rates k) j)) •
        expMeasure (∑ j, completedRates (rates k) j))
    (fallback : γ)
    (hs : ∀ k, model.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start horizon : ℝ) (hstart : start < horizon) (fuel : Nat) (saveEvents : Bool)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : Measurable (fun ts => observable
      (holdingSimulationObservation model states rates marks start horizon fuel saveEvents ts))) :
    (rawWordLaw inputs (fuel + 1)).map
      (fun p => observable (packetCompiledRun P fallback start horizon fuel saveEvents p)) =
    (targetWordLaw (fun l => completedRates (rates l)) marks (fuel + 1)).map
      (fun ts => observable (holdingSimulationObservation model states rates marks start horizon fuel saveEvents ts)) := by
  have hae := packet_raw_driver_executes model algorithm states rates marks P inputs hf hgoodM hgood
    fallback hs start horizon hstart fuel saveEvents
  rw [Measure.map_congr (hae.mono (fun _ h => congrArg observable h))]
  have htarget : independentWordLaw (fun k => (inputs k).map (P.clock k)) (fuel + 1) =
      targetWordLaw (fun l => completedRates (rates l)) marks (fuel + 1) := by
    simp_rw [hlaw]
    have h (k : Nat) : independentWordLaw
        (fun l => ENNReal.ofReal (completedRates (rates l) (marks l) / (∑ j, completedRates (rates l) j)) •
          expMeasure (∑ j, completedRates (rates l) j)) k =
        targetWordLaw (fun l => completedRates (rates l)) marks k := by
      induction k with
      | zero => rfl
      | succ k ih => rw [independentWordLaw, targetWordLaw, ih]
    exact h _
  rw [← htarget, ← raw_word_holding_law inputs hf P.clock hclock (fuel + 1),
    Measure.map_map hobs (measurable_rawWordHoldings P.clock hclock (fuel + 1))]
  rfl

end JumpProcessesLean.Proofs
