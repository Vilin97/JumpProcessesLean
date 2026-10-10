# Proof interface

Import `JumpProcessesLean` to expose the executable implementation and every checked
result. The real proof root is `Proofs/IIDEndToEnd.lean`; the FloatLib proof root is
`Proofs/FloatEndToEnd.lean`.

## Random input

```text
iidStreams : Measure (ℕ ⊕ ℕ → ℝ)      -- infinite product of Uniform(0,1)
streamTape a b ω = ⟨[ω (inl 0), …, ω (inl (a-1))], [-log ω (inr 0), …, -log ω (inr (b-1))]⟩
floatStreamTape ρu ρe a b ω = ⟨[ρu (ω (inl i))]_{i<a}, [ρe (ω (inr i))]_{i<b}⟩
```

`ω (inl i)` is the `i`th uniform draw; `ω (inr i)` is the uniform behind the `i`th
exponential draw. Both tapes are consumed by the public `tapeSource`. The rounding maps
`ρu ρe : ℝ → Binary64` are arbitrary.

## Model conditions

`ModelConsistency model transition rates lower upper` requires:

| Field | Requirement |
| --- | --- |
| `nonnegative` | Every propensity is nonnegative |
| `bounds_valid` | `0 ≤ lower ≤ rates ≤ upper` channelwise |
| `rates_eq` | The model returns the specified finite propensity array |
| `bounds_eq` | The model returns the specified bound arrays |
| `transition_eq` | Every indexed transition returns the specified successor |

These are model conditions, not sampler laws. The channel count `n+1` is fixed. The
state type need not be finite or measurable. Observables are arbitrary functions of
the trace observation (`Except Error (TraceObservation ℝ σ)`) into a measurable space.
The hypothesis `hobs` only requires that, along each reaction word, the observable is
a measurable function of the holding times.

## Exact real laws (`IIDEndToEnd.lean`, `DirectIID.lean`, `NRMIID.lean`)

```text
direct_iid_simulation_law :
  fuel+1 ≤ a → fuel+1 ≤ b →
  iidStreams.map (observable ∘ observeRun ∘ simulate ℝ tapeSource model .direct … (streamTape a b ·) fuel save cap)
    = targetSimulationLaw model transition rates initial start horizon fuel save observable

nrm_iid_simulation_law :
  (n+1)(fuel+1) ≤ b → (same with .nrm) = targetSimulationLaw …

iid_direct_nrm_same_law :
  Direct law = NRM law = targetSimulationLaw = nativeSimulationLaw (any algorithm), a probability measure
```

`targetSimulationLaw` sums over reaction words the marked-exponential holding-time law
`targetWordLaw`, observed through the deterministic stopped replay
`holdingSimulationObservation`. This replay uses the driver's own validation, horizon
stopping, absorbing stopping, transitions, recording choice and event budget. Every
outcome is retained, including transition errors and `eventLimit`. At an absorbing
state the probability completion of `completedRates` is never executed.

The proof does not assume a reaction-word decomposition of the input:

1. `iidStreams_split` and `StreamReader.regenerate`: after any stopping reader, the
   unread streams are IID and independent of the value read.
2. `readerParse_law`: blocks read sequentially are independent with the readers'
   laws.
3. Word events: `directWordEvent`, `nrmWordEvent`, `rssaWordEvent`.
   * They are pairwise disjoint: `*_disjoint` uses uniqueness of the native CDF
     selection, strict NRM race and first acceptance.
   * Their probabilities sum to one: `*_total` uses `path_word_weights_normalize`.
4. `*_stream_driver_executes`: on each word event the public driver executes the
   parsed transcript, with any unread tape suffix.
5. Branch laws: `directWordEvent_branch`, `nrmWordEvent_branch`
   (`nrmRawPathLaw_eq_restrict`), `rssaWordEvent_branch`. Each parsed branch has the
   primitive word measure, whose holding times have the target law.
6. `iid_word_decomposition` assembles the pushforward.

NRM rows read the exponential sources that the native update consumes, given by
`freshPattern`: active channels at initialization; the fired and reactivated channels
after each event. Every other coordinate comes from the unused uniform stream
(`nrmRowReader_law`), so rows are IID. The persistent cache law along each word,
including inactive, activated and deactivated channels, is `masked_cached_word_law`.

## Fixed-cap RSSA (`RSSAIID.lean`, `IIDEndToEnd.lean`)

With cap `N`, `2N(fuel+1) ≤ a` and `N(fuel+1) ≤ b`, let

```text
good = rssaCapGood …  -- realized word ∩ every first-success block uses ≤ N proposals
δ_N  = rssaCapDefect … = iidStreams goodᶜ
```

`rssa_iid_capped_simulation_law` proves three statements:

* `(iidStreams.restrict good).map F ≤ target`;
* `target S ≤ (iidStreams.restrict good).map F S + δ_N`;
* `target S - δ_N ≤ iidStreams (F⁻¹ S) ≤ target S + δ_N` for every measurable `S`.

`rssaCapDefect_tendsto_zero` proves `δ_N → 0`, and `iid_rssa_tendsto_target` gives
`iidStreams (F_N⁻¹ S) → target S`. The reader is `rssaReader`. `rssaReader_law`
identifies its law with the first-success stopping measure `rssaStoppingInputs`, and
`iidStreams_all_rejected` gives the rejection-run probabilities `(1-A/B)^N`.

## FloatLib approximation (`FloatIIDStop.lean`, `FloatEndToEnd.lean`)

The hypotheses are:

* `FloatModelConsistency mf transition ratesF lowerF upperF` for the FloatLib model;
* `ModelConsistency mr transition (floatReal ∘ ratesF) (floatReal ∘ lowerF) (floatReal ∘ upperF)`
  for the real model;
* matching transitions: `htransition : ∀ x i, mf.transition x i = mr.transition x i`;
* real start before the real horizon: `sr < hr`.

| Algorithm | Certificate event | Pathwise theorem | Law theorem |
| --- | --- | --- | --- |
| Direct | `directFloatStopGood` (`DirectStopConditions`) | `direct_float_iid_stop_close` | `direct_float_iid_stop_law_bounds` |
| NRM | `nrmFloatMaskedGood` (`NRMMaskedConditions`) | `nrm_float_iid_masked_close` | `nrm_float_iid_masked_law_bounds` |
| Capped RSSA | `rssaFloatStopGood` (`RSSAStopConditions`, cap, reader support) | `rssa_float_iid_stop_close` | `rssa_float_iid_stop_law_bounds` |

Each certificate is evaluated on the primitive blocks parsed along the realized real
word. It constrains primitive inputs, rounded draws, evaluated arithmetic
expressions, numerical budgets and branch/horizon margins. It contains no assumed
sampler law and no output agreement.

**Stop index.** Every certificate carries `m ≤ fuel+1`. Steps `k < m` carry the
one-event certificate. If `m ≤ fuel`, step `m` is an absorbing state:

* Direct: valid rates whose finite float total is not positive (`direct_float_absorbing`);
* RSSA: valid bounds and no active float rate (`rssa_float_absorbing`);
* NRM: every float rate inactive, so every masked cache entry is `none` and the native
  race reports absorption (`nrm_float_absorbing_cache`).

The Direct and RSSA events also require the real total rate to be zero at `m`; the
NRM event derives it. `scheduled_concrete_run_absorb` and
`simulate_float_schedule_close_absorb` run the public driver through a schedule that
ends in an absorbing state. `direct_float_trajectory_close_stop` and
`rssa_float_trajectory_close_stop` instantiate them for any unread tape suffix.

**Masked NRM cache.** `nrmFloatCacheM` stores `none` for each inactive channel, as the
native cache does, and inactive channels consume no draw.

* `nrm_float_initialize_masked`: native initialization reads one rounded exponential
  per active channel (`nrmFloatInitTape`).
* `nrm_float_winner_masked`: the native race over the active clocks selects the
  certified winner.
* `nrm_float_masked_cache_errors`: the clock error recurrence for active channels is
  proved by induction from the update certificates.
* `nrm_float_masked_trajectory_close`: these combine into the trajectory theorem,
  with the stop index, through the public driver.

On the real side, `nrm_real_clocksM_raw_schedule` identifies the masked real clocks
with the persistent cache of the primitive probability proof for every active
channel.

**Pathwise theorems.** They return the realized word and prove two facts. First, the
real public run equals the deterministic replay of the parsed transcript, stopped at
`m` (`packet_real_replay_stop_eq_holdings`, `nrm_masked_real_replay_eq_holdings`).
Second, the FloatLib public run on `floatStreamTape` is `TraceClose δ` to that real run.

**Law theorems.** For any observables with
`TraceClose δ f r → |Tf f - T r| ≤ ε ∧ If f = I r`, they state:

```text
target (jointTail (t+ε) i) ≤ iidStreams {t < Tf(F) ∧ If(F) = i} + β
iidStreams {t < Tf(F) ∧ If(F) = i} ≤ target (jointTail (t-ε) i) + β
```

Here `β = iidStreams (good)ᶜ` and `target` is the real target law with the decoded
binary64 rates. Outer measures are used for FloatLib events, so no measurability of
FloatLib outputs is assumed. The generic comparison is `word_coupling_tail_bounds`.
`iid_float_direct_approximates_real` and `iid_float_nrm_approximates_real` replace
`target` by the law of the public real simulator on the same streams, using
`direct_iid_simulation_law` and `nrm_iid_simulation_law`.

`recorded_trace_observables_close` instantiates the observable condition with `ε = δ`,
for any recorded timestamp together with the terminal state/count/error outcome.

**Positive-rate special case.** `FloatIID.lean` keeps the earlier events
`directFloatGood`, `nrmFloatGood` and `rssaFloatGood`, with theorems
`*_float_iid_close` and `*_float_iid_law_bounds`. These events require positive rates at
every step, and every NRM channel active. `directFloatGood_subset_stop`,
`rssaFloatGood_subset_stop` and `nrmFloatGood_subset_masked` embed them in the new
events. `iid_float_stop_failure_le` therefore bounds each new `β` by the old one.

**Scope.** Within the certificates:

* all three algorithms may reach an absorbing state within the event budget;
* NRM channels may be inactive, deactivated or reactivated along the word;
* Direct needs a positive total rate at every certified step before the stop;
* RSSA needs an accepted proposal at every certified step before the stop.

No theorem bounds `β` numerically for a specific model.

## Tree-RSSA (`TreeRSSA.lean`, `TreeRSSA/Gen*.lean`, `Proofs/TreeRSSA*.lean`)

Tree-RSSA is RSSA on mass-action networks with JumpProcesses.jl's species population
brackets and a binary sum tree over the upper propensity bounds. A species below its
maximal reactant stoichiometry `maxStoich` gets the exact bracket `[n, n]`, so the upper
total is positive exactly when some reaction is enabled. The specification
`TreeRSSA.simulate op src net …` is generic in the arithmetic and the random source. It
selects a candidate by descending the segment tree (`segSum`, `segDescend`), thins it
with the lower and exact propensities, and accumulates one exponential per proposal.

**In the reals.** For networks with in-range species and nonnegative rate constants
(`ValidNetwork`) and an initial state whose brackets hold (`Bracketed`):

* `segDescend_eq_weightedIndex`: the tree descent returns the index of the linear
  cumulative search used by the public driver;
* `treeRSSA_simulate_eq`: `TreeRSSA.simulate realArithmetic src` is the public
  `simulate … .rssa` on the bracket model, for every random source `src`;
* `bracketModel_consistency`: that model satisfies the driver's consistency conditions
  (nonnegative rates, `lower ≤ rate ≤ upper`, enabled exactly when the upper bound is
  positive), so all RSSA results above apply;
* `tree_rssa_iid_capped_law`: on the IID streams, with proposal cap `N`, every event
  probability is within the cap defect `δ_N` of the target stopped-path law;
* `tree_rssa_tendsto_direct`: as `N → ∞`, every event probability converges to that
  of the public Direct simulator (Gillespie's SSA) on the same streams.

**On host floats.** `hostArithmetic` is Lean's `Float` and `hostSource` draws from
xoshiro256++ (`HostFloat.lean`): uniforms from a word's top 53 bits, exponentials by a
256-layer ziggurat (Marsaglia and Tsang, the method of Julia's `randexp`) whose rare slow path
makes one tail or wedge attempt and otherwise returns `-log V` of a fresh uniform. Each branch
yields an exact `Exp(1)` sample in real arithmetic, so the mixture is `Exp(1)`; the tables are
binary64 roundings of the exact layer widths. Generation `K` is an optimized implementation in
`TreeRSSA/GenK.lean`. `genK_simulate_eq` proves that, for every network whose reactant
species are in range (`ReactantsInRange`) and every input, `GenK.simulate` returns
exactly `TreeRSSA.simulate hostArithmetic hostSource` with the same arguments. These
proofs reason about Lean's logical model of `Float` and use no floating-point identity:

* the flat tree: `TreeOK` (leaves, and every internal node the sum of its children)
  is established by `buildTree_ok` and preserved by `TreeOK.update`, `fixPath_spec`,
  `fixUntil_spec` and `setBounds_spec`. `TreeOK.descend` shows the array descent is the
  specification's `segDescend`; `treeOK_unique` shows the tree is determined by its
  leaves and its unused slot `0`;
* generations 1 to 3 maintain the cache invariant `CacheOK`: the lower bounds and the
  tree of upper bounds of the specification state (`refresh_ok`, `gen2_refresh_ok`,
  `gen3_refresh_ok`);
* generation 4 reorganizes the control flow (`run_eq`, `start_eq`, no invariant);
* generation 5's refresh returns exactly generation 3's cache (`gen5_refresh_eq`). A
  skipped bound has an unchanged integer factor, and `evalAt_set` reads the old factor
  from the updated arrays;
* generations 6 to 16 are proved equal to their predecessors (`gen6_eq_gen5` …
  `gen16_eq_gen15`). Generation 7 uses `isFinite_eq_lt`: a float is finite exactly when
  it lies strictly between the two infinities, by the same case analysis in Lean's model of
  `compare` and `isFinite`;
* generation 11's machine-word descent visits the nodes of `Gen1.descend`: from node `1` a
  node of level `i` lies in `[2^i, 2^(i+1))`, so the test `k < P` fails exactly after `depth`
  levels (`descendW_eq`);
* generation 12 carries each new node sum up the path and reads only the sibling.
  `float_add_comm` proves float addition commutative in Lean's model (not-a-number carries
  no payload; finite values add as integers at the smaller exponent), so the sum is the
  same whichever child the path comes from (`fixUntilGo_eq`, `fixPathGo_eq`);
* generation 13 compiles each dependent's factor into an integer code, from which the
  refreshed species' power and the partner factor are recovered (`code_eval`);
* generation 14 tests the tree size once per proposal and otherwise runs generation 13's
  proposal (`gen14_eq_gen13`);
* generation 15 fires on machine words with carried size facts: its loop computes the fold of
  the changes (`applyFrom_val`), and the refresh fold is skipped only when every refresh would
  return the cache it is given (`anyStale_false`, `foldRefresh_id`, `fire15_eq`);
* generation 16 refreshes on machine words with the refreshed species' powers precomputed;
  `a p = b p` iff `a = b` or `p = 0`, so its test of a changed bound is generation 13's
  (`mul_eq_ite`, `setBounds16_eq`).

The trust base for executable Tree-RSSA is Lean's: compiled code runs the C
implementations of the `@[extern]` float operations (including `log` and `exp` from the C
library) for the logical `Float` model. xoshiro256++ is a pseudo-random generator, and no
theorem claims that its outputs are independent uniforms. The laws above are proved for
ideal IID streams in the reals.

## Rounding and execution lemmas

`binary64_add_eq_spec` and `binary64_div_eq_spec` identify the executable operations
with FloatLib's nearest-even specification. `float_add_error`, `float_sub_error`,
`float_mul_error`, `float_div_error`, `float_fold_sum_error`,
`float_clock_time_error` and `float_nrm_rescale_error` give the half-ULP budgets used
by the certificates. `chooseAux_float_margin`, `nrm_float_winner_approx` and
`rssa_float_accept_stable` prove decision stability under margins.

## Checking trust and tests

```bash
bash scripts/verify.sh
```

This builds the proofs, runs the native FloatLib test suite, audits the dependencies
of the 275 results listed in `Tests/Trust.lean`, and runs the original pinned Julia
method fixtures. The audit permits only Lean's standard `propext`, `Classical.choice`
and `Quot.sound`, and rejects `sorry`, `admit`, `axiom`, `unsafe` and `native_decide`
in project sources.

The upstream SciML integration suite, callbacks, variable-rate jumps, and
infinite-time/nonexplosion extensions are outside this translation's scope.
