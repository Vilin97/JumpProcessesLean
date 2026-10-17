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
* generations 6 to 18 and 20 to 29 are proved equal to their predecessors (`gen6_eq_gen5` …
  `gen18_eq_gen17`, `gen20_eq_gen19` … `gen29_eq_gen28`), and generation 19 to generation 17
  (`gen19_eq_gen17`). Generation 7 uses `isFinite_eq_lt`: a float is finite exactly when
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
* generation 17 keeps of each group of range tests only those that imply the others in Lean's
  float model (`uniform_checks`, `exponential_checks`, `time_checks`). It fires in one loop that
  tests each changed species on the side it moved to: with no species outside its bracket before
  the event and distinct species per reaction, this is the fold of the changes followed by
  generation 15's test (`staleI_up`, `staleI_down`, `applyTest_eq`, `fire17`). A refresh puts its
  species inside the bracket of its own count and moves no other bracket, so the invariant holds
  after every event (`foldRefresh13_brackets`), and without a refresh the tree, hence the total,
  is unchanged (`RunInv`, `gen17_run_eq`). The start tests these conditions and otherwise runs
  generation 16 (`start17_eq`).
* generation 18 holds the populations, the brackets and the maximal stoichiometries as the
  floats `Float.ofNat x` of counts below `2^26` (`CountsOf`). `Proofs/NativeCounts.lean` proves
  that on such floats the native sum, the difference of a larger and a smaller count, the
  product below `2^53` and the comparisons are those of the natural numbers (`count_add`,
  `count_sub`, `count_mul`, `count_lt`, `count_le`, `count_beq`), through FloatLib's bridge
  from Lean's float model to binary64 rounding (`toModel_ofFloat_add_of_isFinite`,
  `roundDyadic_of_representable`) and an ordering lemma: the model compares finite positive
  floats by exponent, then mantissa (`count_compare`). So generation 18's firing
  (`applyW_eq`), staleness test (`staleW_eq`), refresh (`setBoundsW_eq`, `refreshFrom_eq`)
  and acceptance test (`acc18_eq`) compute generation 17's on the floats of its counts, and a
  bound's float product is `natToFloat` of generation 17's integer factor. Counts stay below
  `2^26`: when a changed count reaches `2^25`, that event's refresh and the rest of the run are
  generation 17's (`run18_eq_of`). The start tests that the network's factors have order at
  most two and the counts, brackets and change amounts are below `2^26`, and otherwise runs
  generation 17 (`start18_eq`).
* generation 19 is generation 18 without lower bounds. Generation 17's lower bounds are the
  propensities at the brackets' lower ends (`CacheOK`); every firing keeps this, through the
  equalities of the earlier generations' firings with generation 3's (`fire13_cacheOK`), and no
  species leaves its bracket (`fire17`). For factors of order at most two the integer factor is
  monotone in every count (`eval_mono`). Lean's float comparisons are transitive, since
  `compare` is lexicographic in sign class, exponent and mantissa (`float_le_trans`,
  `float_lt_of_lt_of_le`), and multiplication by a rate `0 ≤ r < 2^52` is monotone on counts
  below `2^53`: it is the exact product rounded once, and rounding is monotone (`mul_count_mono`,
  through FloatLib's bridge). So the lower-bound test accepts only proposals that the exact test
  accepts (`squeeze_redundant`), and generation 17's acceptance is generation 19's (`acc19_eq`,
  `gen19_run_eq`). The start also tests the rates and otherwise runs generation 17
  (`start19_eq`).
* generation 20 is generation 19 with every array access in bounds by proof. Its start tests the
  compiled records once (`boundsOK_spec`: changed species and factors' species below the species
  count, dependents' leaves below `P`); its driver carries the sizes of the counts, brackets and
  tree, which firing and refreshes keep (`applyU_size`, `refreshFromU_sized`). An access in
  bounds reads and writes what generation 19's tested access does (`fget_uget`, `cset_uset`), so
  each loop is generation 19's (`applyU_eq`, `setBoundsU_eq`, `refreshFromU_eq`) and, with the
  tree's size carried, so is the driver (`gen20_run_eq`, `start20_eq`).
* generation 21 reads each proposed reaction from one record holding its rate, its factor and
  its two or three changes, built once at the start (`buildRx`). A record holds its reaction
  (`RxAt`, by `rxOf_at` from the array's definition), so its fields are what generation 19's
  tested accesses read (`rx_rate`, `rx_eval`), and its steps over the changes are generation
  19's loops unrolled (`applyR_eq`, `smallR_eq`, `refreshFromR_eq`). The drivers agree
  (`gen21_run_eq`), and the start runs generation 20 when a reaction changes fewer than two
  or more than three species (`start21_eq`).
* generation 22 descends two levels per step on trees of `2^12` leaves or more. A node `d`
  levels above the leaves of a tree with `P = 2^n` leaves (`Level`) has its grandchildren in
  range, and two steps of the one-level descent read the left child and then one grandchild
  by the first comparison, so the two-level descent returns the same leaf (`descend2_eq`). Its
  walks and refreshes, compiled in its own module, are generation 21's (`fixUntilR_eq`,
  `setBoundsR22_eq`), and so is the driver (`gen22_run_eq`); the start runs generation 21
  unless the leaves number `2^depth` (`start22_eq`).
* generation 23 descends two levels per step from `2^9` leaves instead of `2^12`; its descents,
  compiled in its module, are generation 22's (`descendW23_eq`, `Gen23.descend2_eq`), and the
  rest of its driver is generation 22's (`gen23_run_eq`, `start23_eq`).
* generation 24 ends the two-level descent with a pair of levels computed as `4k + c`, the offset
  `c` from the three comparisons the word descent makes there; `Gen24.descend2_eq` shows the
  leaf is the word descent's (`4k + c` is `2(2k) + …` below `2P`), and the rest of the driver
  is generation 23's (`gen24_run_eq`, `start24_eq`).
* generation 25 reads the brackets from the cache inside each firing step and builds states and
  the fallback cache in calls, definitional rewrites of generation 24's driver (`applyRC_eq`,
  `gen25_run_eq`). Its start tests generation 24's conditions at once and otherwise calls
  generation 21's start; the starts of generations 22 to 24 test the same conditions, so they
  fall through to it as well (`start25_eq`).
* generation 26's records hold one, two or three changes; its firing, small-count test and
  refresh apply the changes array in order (`applyRV_eq`, `smallV_eq`, `refreshFromRV_eq`), so
  its driver is generation 25's (`gen26_run_eq`). On a network with a reaction of one change it
  runs its own driver where generation 25 falls through generation 21's start to generation
  20's; both drivers agree with generation 19's (`start26_eq`).
* generation 27 runs generation 26's driver on inputs built with less work. Its compile is
  generation 6's (`compile27_eq`): its factor compiler reads the reactants without a list
  (`factorOf_eq`), and a dependent's factor read from its reaction's, with `.general #[]` past
  the last reaction, is the factor compiled from the reaction at that index. Its initial tree
  is `Gen1.buildTree`'s (`initialTree_eq`), and its start, on a cache without lower bounds,
  returns generation 26's start on the cache with them: the fast path never reads them and
  the fallback computes them (`start27_eq`).
* generation 28's start compares the species of up to three changes directly, which decides
  `List.Nodup` of their list (`distinctSpecies_eq`); its `changesOK` is therefore generation
  17's (`changesOK28_eq`) and its start generation 27's (`start28_eq`).
* generation 29's refresh walks first re-add eleven levels without testing whether they met
  the path of the next changed leaf. Its trees then differ from generation 26's only at strict
  ancestors of the pending leaf (`AgreeOff`): up to the meeting point both walks write the same
  sums, and past it generation 29's writes only ancestors of the next leaf, whose walk writes
  them again (`walkFixed_agree`). The last walk of a refresh writes every ancestor of its leaf,
  so the trees agree when the refresh ends (`fixPath_agree`, `setBoundsR29_eq`), and the
  driver returns generation 26's (`gen29_run_eq`).

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

A new clock passes its test (`clockFlag` and its NRM and Direct forms) when it is finite and
no earlier than the current time. A step of at most half an ulp of the current time rounds
to it; `float_clock_time_error` bounds that rounding like any other, so the certificates and
their time budgets cover such a step, and the real replay is unchanged.

## Checking trust and tests

```bash
bash scripts/verify.sh
```

This builds the proofs, runs the native FloatLib test suite, audits the dependencies
of the 354 results listed in `Tests/Trust.lean`, and runs the original pinned Julia
method fixtures. The audit permits only Lean's standard `propext`, `Classical.choice`
and `Quot.sound`, and rejects `sorry`, `admit`, `axiom`, `unsafe` and `native_decide`
in project sources.

The upstream SciML integration suite, callbacks, variable-rate jumps, and
infinite-time/nonexplosion extensions are outside this translation's scope.
