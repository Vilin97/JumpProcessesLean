# Proof interface

Import `JumpProcessesLean` to expose the executable implementation and every checked
result. The real proof root is `Proofs/IIDEndToEnd.lean`; the FloatLib proof root is
`Proofs/FloatIID.lean`.

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

## FloatLib approximation (`FloatIID.lean`)

The hypotheses are:

* `FloatModelConsistency mf transition ratesF lowerF upperF` for the FloatLib model;
* `ModelConsistency mr transition (floatReal ∘ ratesF) (floatReal ∘ lowerF) (floatReal ∘ upperF)`
  for the real model;
* matching transitions: `htransition : ∀ x i, mf.transition x i = mr.transition x i`;
* real start before the real horizon: `sr < hr`.

| Algorithm | Certificate event | Pathwise theorem | Law theorem |
| --- | --- | --- | --- |
| Direct | `directFloatGood` (`DirectTrajectoryConditions`) | `direct_float_iid_close` | `direct_float_iid_law_bounds` |
| NRM | `nrmFloatGood` (`NRMTrajectoryConditions`) | `nrm_float_iid_close` | `nrm_float_iid_law_bounds` |
| Capped RSSA | `rssaFloatGood` (`RSSATrajectoryConditions`, cap, reader support) | `rssa_float_iid_close` | `rssa_float_iid_law_bounds` |

Each certificate is evaluated on the primitive blocks parsed along the realized real
word. It constrains primitive inputs, rounded draws, evaluated arithmetic
expressions, numerical budgets and branch/horizon margins. It contains no assumed
sampler law and no output agreement.

The pathwise theorems return the realized word and prove two facts. First, the real
public run equals the deterministic replay of the parsed transcript. Second, the
FloatLib public run on `floatStreamTape` is `TraceClose δ` to that real run.

The law theorems state, for any observables with
`TraceClose δ f r → |Tf f - T r| ≤ ε ∧ If f = I r`:

```text
target (jointTail (t+ε) i) ≤ iidStreams {t < Tf(F) ∧ If(F) = i} + β
iidStreams {t < Tf(F) ∧ If(F) = i} ≤ target (jointTail (t-ε) i) + β
```

Here `β = iidStreams (good)ᶜ` and `target` is the real target law with the decoded
binary64 rates; by `iid_direct_nrm_same_law` it is also the law of the real Direct and
NRM simulators on the same streams. Outer measures are used for FloatLib events, so
no measurability of FloatLib outputs is assumed. The generic comparison is
`word_coupling_tail_bounds`.

`recorded_trace_observables_close` instantiates the observable condition with `ε = δ`,
for any recorded timestamp together with the terminal state/count/error outcome.

**Scope.** The float certificates require:

* NRM: positive decoded rates along the certified word (no inactive channels);
* Direct: a positive total rate at every certified step;
* RSSA: an accepted proposal at every certified step.

Words that reach an absorbing state within the event budget are counted in `β`. No
theorem bounds `β` numerically for a specific model.

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
of the 148 results listed in `Tests/Trust.lean`, and runs the original pinned Julia
method fixtures. The audit permits only Lean's standard `propext`, `Classical.choice`
and `Quot.sound`, and rejects `sorry`, `admit`, `axiom`, `unsafe` and `native_decide`
in project sources.

The upstream SciML integration suite, callbacks, variable-rate jumps, and
infinite-time/nonexplosion extensions are outside this translation's scope.
