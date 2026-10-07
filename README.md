# JumpProcessesLean

Lean translations of JumpProcesses.jl's Direct, NRM, and RSSA using FloatLib binary64 arithmetic and a shared real interpretation.

**Status:** executable one-event laws and finite reaction-word laws with a persistent NRM cache are checked, including inactive, activated and deactivated channels. Direct and NRM initialization/selection have float distribution approximations. The refinement of the concrete simulation driver and complete float trajectory bounds are **not finished**.

## Build and test

Install Elan and Julia 1.11 or later, then run `bash scripts/verify.sh`. It runs `lake build`, `lake test`, the Lean theorem dependency audit, and the original Julia fixtures, writing logs to `results/`. The first native build compiles FloatLib's C dependencies. Toolchain and dependency revisions are pinned.

## Translation scope

Models are finite homogeneous pure jump systems. Rates can depend on the state and remain constant between jumps. Models supply rates, indexed transitions, and enclosing bounds. Population brackets and mass-action helpers are included.

| Algorithm | Preserved mechanism | Implementation choice |
| --- | --- | --- |
| Direct | Cumulative selection and a total-rate exponential | Strict CDF endpoints skip zero-rate channels |
| NRM | Persistent clocks, fresh fired/reactivated clocks, residual rescaling | Linear argmin; simulation uses the complete dependency graph |
| RSSA | Upper-rate proposals, lower acceptance shortcut, accumulated Exp(1) clocks | Bounds checked per event; proposal exhaustion reports an error |

Inactive NRM clocks use `none` and do not consume initial exponential draws. Seeded trajectories need not match Julia, which uses a different RNG and infinity representation. Duplicate dependencies consume no extra samples. Full-graph NRM updates traverse channels recursively in index order; partial graphs use the indexed loop. Every rescaling uses the old state.

The scope excludes the SciML integrator/callback framework, ODE/SDE coupling, variable-rate jumps, GPU support, heap optimization, and cached RSSA species/dependency bracket updates.

All default simulation arithmetic and logarithms use FloatLib. SplitMix64 is a reproducible executable source; there is no theorem claiming it is an IID continuous source. The optional certified source propagates logarithm certification failure.

## Executable real laws

For rates `a_i`, total `A = ∑ i, a_i > 0`, and `t ≥ 0`, the target is

```text
P(T > t, I = i) = (a_i / A) exp(-A t).
```

Independent uniforms on `(0,1)` are transformed by `-log(u)/rate`. Lean derives the actual CDF selector, actual NRM initialization/minimum, and actual RSSA first-success recursion. The main equality covers every Borel time set and reaction index.

| Checked result | Main theorem / module |
| --- | --- |
| Actual Direct marked exponential law, allowing zero channels | `direct_real_clock_law`, `RealSamplerLaws.lean` |
| Actual positive-rate NRM initialization/minimum law | `nrm_uniform_clock_law`, `RealSamplerLaws.lean` |
| Actual RSSA selection/acceptance probability | `proposalMark_probability`, `RSSABranches.lean` |
| First-success recursion consumes the tape and accumulates the correct clock | `rssa_first_success_executes`, `rssa_uniform_branch_executes` |
| Exponential sums have Erlang laws, derived by convolution | `sum_exponentials_erlang`, `ExponentialSum.lean` |
| Infinite sum of actual validated RSSA branch laws equals the target | `rssa_validated_executable_law`, `RSSABranches.lean` |
| Equality of all three executable marked time laws | `operational_samplers_same_marked_time_law`, `RealSamplerLaws.lean` |
| Actual capped RSSA failure probability `(1-A/B)^N` | `rssa_cap_failure_probability`, `RSSABranches.lean` |
| Public full-graph NRM update executes fresh/rescaled/disabled clocks, including zero rates | `nrmUpdate_uniform_executes`, `NRMUpdate.lean` |
| Actual positive-rate NRM update has independent exponential residual tails | `nrm_operational_update_invariant`, `NRMUpdate.lean` |
| Full joint law of winner time and the actual updated residual vector | `nrm_actual_transition_full_law`, `NRMTransitionLaw.lean` |

The cache invariant is derived at a random winning time from the primitive product measure, including the fired channel's independent fresh draw. Independence is not supplied as a hypothesis. A finite-vector measure extension theorem turns joint-tail identities into all-Borel residual laws.

`MaskedTransition.lean` extends the full joint cache law to inactive, activated and deactivated channels. Inactive coordinates are unused independent ghost variables: the implementation stores `none`, draws no inactive initialization clock, and excludes them from the race. `masked_history_step_factorization` proves independence of the entire sampled past. `masked_cached_word_law` iterates the actual returned cache. `finite_masked_word_laws_equal` proves equality of all finite reaction-word measures with state-dependent nonnegative rates and positive total rates. These are cylinder laws; the refinement of `simulateLoop` remains separate. Executable absorbing states are covered by deterministic tests.

RSSA equality uses the **unbounded first-success law**, expressed as a sum of successful-branch measures. Capped RSSA has a `proposalLimit` outcome. For valid bounds and `0 < A ≤ B`, its exact real failure mass after `N` proposals is `(1-A/B)^N`; this mass is not discarded or normalized away.

## FloatLib approximation

`FloatApproximation.lean` proves actual binary64 half-ULP bounds for add, subtract, multiply, and divide, including subnormals under its finite-input/output conditions. It proves left-fold, clock-expression, and Gibson–Bruck rescaling budgets. Certified logarithm success gives its rounding bound; the ordinary logarithm has an a-posteriori bound against a successful certificate.

Certificates constrain inputs, finite intermediates, numerical budgets, and branch margins. They do **not** assume output agreement.

* `direct_float_certificate_refines` proves the complete float Direct call preserves the real mark and bounds the time error, including rounded propensity summation.
* `direct_float_joint_tail_approx` proves actual float Direct joint-tail bounds under a coupling certified outside a bad set of mass `β`, with time error `δ` and `t ≥ δ`:

  ```text
  (a_i/A) exp(-A(t+δ)) ≤ P(T_f > t, I_f = i) + β
  P(T_f > t, I_f = i) ≤ (a_i/A) exp(-A(t-δ)) + β.
  ```

  The real target rates are the exact decoded binary64 inputs. Source error is included in the certificate; `β` is the probability of certificate failure.
* `nrm_float_certificate_refines` proves actual float initialization/minimum preserve a winner when its clock gap exceeds twice the numerical budget, and bounds its time error. Source exponential errors are included.
* `nrm_float_joint_tail_approx` gives the corresponding marked-time distribution envelopes for actual FloatLib NRM initialization and minimum selection.
* `chooseAux_float_margin`, `nrm_float_winner_approx`, and `rssa_float_accept_stable` prove stability of the actual CDF, minimum, and acceptance decisions.
* `coupled_joint_tail_bounds` supplies a general approximation inequality with an explicit bad-set probability.

These are conditional approximation results. They do not bound certificate failure for every model, prove SplitMix64 IID correctness, or claim exact continuous sampling by binary64.

## Remaining proof obligations

1. Refine `simulate` / `simulateLoop` and compose the verified laws into finite trajectory laws with state-dependent rates, horizon stopping, transitions, and event limits. The actual positive-rate update invariant is proved; this simulation-level composition is not.
2. Incorporate absorbing states and horizon stopping into the simulation-level composition. The probabilistic cache law now covers inactive, activated and deactivated channels.
3. Prove complete NRM/RSSA float distribution bounds and propagate certificates through whole simulations. Initialization, rescaling, RSSA acceptance, and CDF bounds are checked components.
4. Quantify source/certificate failure probabilities for a chosen finite source. Infinite-path CTMC results also require a nonexplosion hypothesis.

There are no project proof placeholders, extra axioms, `native_decide`, or unsafe code. `Tests/Trust.lean` audits principal results; the script permits only standard Lean `propext`, `Classical.choice`, and `Quot.sound`.

## Test evidence

The successful logs are in `results/`.

* Deterministic FloatLib fixtures cover zero rates, NRM fresh/rescaled/activated/disabled clocks, ties, duplicate dependencies, RSSA rejection-clock accumulation, malformed bounds, proposal exhaustion, mass action, and brackets.
* 20,000 event samples per algorithm test the explicit `[1,3]` joint clock/mark law.
* 8,000 trajectories per algorithm reproduce the upstream linear A→B scenario: 16 channels, A=100, rates 0.1 through 1.6, horizon 0.1, original tolerance 1.
* Conservation, extinction, terminal horizon, and chronological traces are checked.
* A Julia harness executes the pinned original algorithm bodies with 8 deterministic assertions. Integrator/random-tape/heap interfaces are stubbed; the full SciML suite was not run. Vendored sources retain the upstream MIT license.

| Algorithm | Mean (target 0.25) | Variance (target 0.0625) | P(channel 1), zero-based (target 0.75) | A→B mean (target 25.666078) |
| --- | ---: | ---: | ---: | ---: |
| Direct | 0.249413 | 0.063395 | 0.752250 | 25.706750 |
| NRM | 0.249802 | 0.062566 | 0.747800 | 25.659750 |
| RSSA | 0.249844 | 0.061971 | 0.750700 | 25.655750 |

## Pinned revisions

* JumpProcesses.jl: `3c8c8edc8d8a84c47a7200064ab1f2fedd2ee22d`
* FloatLib: `1e83f09ed8c41a953cf8f93d26c210778177b94a`
* Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`
* Lean 4.34.0; Julia fixture runtime 1.11.7.

The project is MIT licensed. Original upstream licensing is in `vendor/JumpProcesses.jl/LICENSE.md`.
