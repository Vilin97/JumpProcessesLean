# Proof interface

Import `JumpProcessesLean` to expose the executable implementation and all checked results. The proof roots are `Proofs/EndToEnd.lean` and `Proofs/FullFloatLaw.lean`.

## Exact real simulation law

`direct_nrm_rssa_simulations_same_law` proves equality of the full observable pushforward for arbitrary algorithms `a` and `b`. It is quantified over the state type, initial state, start/horizon, event budget, recording flag and measurable observable.

The model inputs are given by `ModelConsistency`:

| Field | Requirement |
| --- | --- |
| `nonnegative` | Every propensity is nonnegative |
| `bounds_valid` | Nonnegative lower bounds enclose each propensity with its upper bound |
| `rates_eq` | The model returns the specified finite propensity array |
| `bounds_eq` | The model returns the specified bound arrays |
| `transition_eq` | Every indexed transition returns the specified successor |

These are model conditions, not sampler laws. The channel count is fixed and nonempty. The state type need not be finite. The observable must be measurable after the canonical stopped-path observation.

The target next event has

```text
P(T ∈ S, I=i) = (a_i/A) Exp(A)(S),  A=∑ a_i > 0.
```

The proof derives this from actual operations:

1. Direct: uniform inversion of the total exponential clock and the native CDF selector.
2. NRM: primitive initial uniforms, nullable native argmin, and full native fresh/rescaled/disabled updates. Fubini and the exponential residual law establish independence of the surviving cache and the sampled past. Independence is proved at each winning time.
3. RSSA: IID proposal clocks and mark/acceptance uniforms, restricted to each actual first-success branch. Erlang convolution and the geometric mixture produce `Exp(A)`. The total stopping-input mass is proved to be one.
4. Each source is compiled to a tape consumed by the public `simulate`. NRM retains its native absolute cache. The driver is proved to replay that concrete transcript.
5. Every reaction word is summed. Probability completions at zero total rate are ignored by the native absorbing observation. The common stopped law has mass one.

`native_simulation_law_eq_target` identifies each simulator with that target. `native_simulation_probability` checks normalization. All horizon decisions, event-budget exhaustion and recording choices are part of the observation.

RSSA's exact theorem is for unbounded first-success semantics. Its compiled native call uses a cap sufficient for the finite sampled transcript. A fixed proposal cap has an additional `proposalLimit` outcome, so it cannot have exactly the Direct distribution. `rssa_cap_failure_probability` proves its real one-event failure probability.

## FloatLib approximation

`float_simulations_approximate_same_real_law` compares a FloatLib algorithm `a` to any real algorithm `b`, summing every reaction word. The common real rate is the exact decoded binary64 input propensity. The combined theorem requires positive decoded propensities.

A `FloatModelConsistency` bridge identifies the native float model's arrays and transitions. `ModelConsistency` identifies the decoded real model. Float and real transition functions agree.

`FloatBranchConditions` selects one of three input-only certificates:

| Certificate | Numerical content |
| --- | --- |
| `DirectTrajectoryConditions` | Propensity folds, source error, CDF margins, finite clock expressions, accumulated budget and horizon margins |
| `NRMTrajectoryConditions` | Initial clocks, finite cached expressions, update rounding/source budgets, race gaps, cache budget and horizon margins |
| `RSSATrajectoryConditions` | Bound checks, all rejected/accepted proposal comparisons, source and clock-fold error, cap, accumulated budget and horizon margins |

The certificates constrain primitive inputs and evaluated arithmetic expressions. They contain no assumed sampler distribution or returned-output agreement. The refinement lemmas derive native execution and the trace error.

For NRM, `NRMUpdateConditions` omits prior cache/time error hypotheses. `nrm_float_cache_errors` proves them by induction, then constructs the one-step `NRMUpdateCertificate`. Thus the complete theorem does not assume the error recurrence it needs to establish.

Let `β` be the total input mass of failed certificates, including fixed-cap RSSA failures, and let `ε` bound an observable's error on traces whose timestamp errors are at most `δ`. Then

```text
P_real(T > t+ε, I=i) ≤ P_float(T > t, I=i) + β
P_float(T > t, I=i) ≤ P_real(T > t-ε, I=i) + β.
```

`primitive_float_word_mass` derives each branch's probability. `float_full_bad_mass_le_one` proves `β ≤ 1` by summing all actual primitive branches, with no manual normalization.

`recorded_trace_observables_close` instantiates the observable condition with any recorded timestamp and the terminal state/count/error outcome, using `ε=δ`. Missing timestamps and error outcomes use timestamp zero; paired trace lengths and error outcomes agree.

The rounding results use FloatLib's binary64 semantics and half-ULP bounds, including gradual underflow, under finite-input/intermediate conditions. Source errors and logarithm certification are explicit. The executable SplitMix64 source has deterministic/statistical tests, not a continuous IID theorem.

## Checking trust and tests

```bash
bash scripts/verify.sh
```

This builds the proof roots, executes the native FloatLib test suite, audits all principal theorem dependencies and runs the original pinned Julia method fixtures. `Tests/Trust.lean` prints dependencies for 114 principal results. The audit permits only Lean's standard `propext`, `Classical.choice` and `Quot.sound`.

There are no project proof placeholders or extra postulates. The upstream SciML integration suite, callbacks, variable-rate jumps and infinite-time/nonexplosion extensions are outside this translation's scope.
