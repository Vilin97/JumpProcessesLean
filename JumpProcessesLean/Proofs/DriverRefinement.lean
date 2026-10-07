import JumpProcessesLean.Proofs.NonnegativePathLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

structure TraceObservation (α σ : Type) where
  state : σ
  time : α
  events : Nat
  trace : Array (α × σ)

def observeSolution {α σ R : Type} (s : Solution α σ R) : TraceObservation α σ :=
  ⟨s.state, s.time, s.events, s.trace⟩

def observeRun {α σ R : Type} (r : Except Error (Solution α σ R)) :
    Except Error (TraceObservation α σ) := r.map observeSolution

/-- Deterministic event replay uses the driver's time validation, horizon stopping,
transition and event-budget rules, including its final horizon trace entry. -/
def replayEvents {α σ : Type} (op : Arithmetic α) (model : Model α σ)
    (horizon : α) (saveEvents : Bool) :
    Nat → σ → α → Nat → Array (α × σ) → List (Event α) → Except Error (TraceObservation α σ)
  | _, state, _, count, trace, [] => .ok ⟨state, horizon, count, trace.push (horizon, state)⟩
  | fuel, state, now, count, trace, e :: rest => do
    if !op.le now e.time || !op.finite e.time then throw .invalidTime
    if !op.le e.time horizon then
      return ⟨state, horizon, count, trace.push (horizon, state)⟩
    match fuel with
    | 0 => throw .eventLimit
    | fuel + 1 =>
      let newState ← model.transition state e.reaction
      let trace := if saveEvents then trace.push (e.time, newState) else trace
      replayEvents op model horizon saveEvents fuel newState e.time (count + 1) trace rest

/-- A finite primitive execution transcript. Each premise is a concrete sampler or
cache-update call, not an assumed probability law or a final-output equality. The
last sampled event is retained when the event budget is exhausted. -/
inductive ConcreteRun {α σ R : Type} [Inhabited α] (op : Arithmetic α)
    (src : RandomSource α R) (model : Model α σ) (algorithm : Algorithm) (maxProposals : Nat) :
    Nat → σ → α → R → Option (NRMState α) → List (Event α) → Prop
  | absorb {fuel state now rng cache rng'}
      (sample : sampleEvent op src model algorithm maxProposals state now rng cache = .ok (none, rng')) :
      ConcreteRun op src model algorithm maxProposals fuel state now rng cache []
  | budget {state now rng cache rng'} {e : Event α}
      (sample : sampleEvent op src model algorithm maxProposals state now rng cache = .ok (some e, rng')) :
      ConcreteRun op src model algorithm maxProposals 0 state now rng cache [e]
  | next {fuel state now rng cache rng' newState newCache newRng} {e : Event α} {rest}
      (sample : sampleEvent op src model algorithm maxProposals state now rng cache = .ok (some e, rng'))
      (transition : model.transition state e.reaction = .ok newState)
      (update : refreshCache op src model algorithm newState e rng' cache = .ok (newCache, newRng))
      (tail : ConcreteRun op src model algorithm maxProposals fuel newState e.time newRng newCache rest) :
      ConcreteRun op src model algorithm maxProposals (fuel + 1) state now rng cache (e :: rest)

/-- Refinement of the actual recursive simulation driver. The observation includes
every recorded state and timestamp, the terminal horizon and event-limit errors. -/
theorem simulateLoop_refines_replay {α σ R : Type} [Inhabited α] (op : Arithmetic α)
    (src : RandomSource α R) (model : Model α σ) (algorithm : Algorithm)
    (horizon : α) (saveEvents : Bool) (maxProposals fuel : Nat) (state : σ) (now : α)
    (rng : R) (cache : Option (NRMState α)) (events : List (Event α))
    (h : ConcreteRun op src model algorithm maxProposals fuel state now rng cache events)
    (count : Nat) (trace : Array (α × σ)) :
    observeRun (simulateLoop op src model algorithm horizon saveEvents maxProposals
      fuel state now rng cache count trace) =
    replayEvents op model horizon saveEvents fuel state now count trace events := by
  induction h generalizing count trace with
  | absorb sample =>
    rw [simulateLoop, sample]
    simp [observeRun, observeSolution, Except.map, replayEvents, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | budget sample =>
    rw [simulateLoop, sample]
    simp only [Bind.bind, Except.bind]
    rw [replayEvents]
    split
    · simp_all [observeRun, observeSolution, Except.map, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    · split <;> simp_all [observeRun, observeSolution, Except.map, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  | next sample transition update tail ih =>
    rw [simulateLoop, sample]
    simp only [Bind.bind, Except.bind]
    rw [replayEvents]
    split
    · simp_all [observeRun, observeSolution, Except.map, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    · split
      · simp_all [observeRun, observeSolution, Except.map, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
      · simp only [transition, Bind.bind, Except.bind, Pure.pure, Except.pure]
        rw [update]
        simp only [Except.bind]
        exact ih _ _

/-- Refinement of the public wrapper, after its real start/horizon validation and
actual algorithm-specific initialization. -/
theorem simulate_refines_replay {σ R : Type} (src : RandomSource ℝ R)
    (model : Model ℝ σ) (algorithm : Algorithm) (initial : σ) (start horizon : ℝ)
    (hstart : start < horizon) (rng initializedRng : R) (cache : Option (NRMState ℝ))
    (maxEvents maxProposals : Nat) (saveEvents : Bool) (events : List (Event ℝ))
    (hinit : initializeCache realArithmetic src model algorithm initial start rng =
      Except.ok (cache, initializedRng))
    (hrun : ConcreteRun realArithmetic src model algorithm maxProposals
      maxEvents initial start initializedRng cache events) :
    observeRun (simulate realArithmetic src model algorithm initial start horizon rng
      maxEvents saveEvents maxProposals) =
      replayEvents realArithmetic model horizon saveEvents maxEvents initial start 0 #[(start, initial)] events := by
  unfold simulate
  have hvalid : (realArithmetic.finite start && realArithmetic.finite horizon &&
      realArithmetic.le start horizon) = true := by simp [realArithmetic, hstart.le]
  have hp : realArithmetic.lt start horizon = true := by simp [realArithmetic, hstart]
  simp only [hvalid, hp, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hinit]
  simp only [Bind.bind, Except.bind]
  exact simulateLoop_refines_replay _ _ _ _ _ _ _ _ _ _ _ _ _ hrun _ _

end JumpProcessesLean.Proofs
