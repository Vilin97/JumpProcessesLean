import JumpProcessesLean.Proofs.FloatIIDStop
import JumpProcessesLean.Proofs.IIDEndToEnd

/-!
# FloatLib simulators against the real simulators on the same IID streams

The public FloatLib Direct and NRM simulators read the IID streams through rounding
maps. Their joint tail probabilities are within the certificate failure probability
`β` of the law of the public real simulators on the same streams, which is the exact
target law (`iid_direct_nrm_same_law`). The certificates allow absorbing states, and
for NRM inactive channels.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- The public FloatLib Direct simulator approximates the law of the public real Direct
simulator on the same IID streams, through absorbing states. -/
theorem iid_float_direct_approximates_real {σ ι : Type} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (a b : ℕ) (ha : fuel + 1 ≤ a) (hb : fuel + 1 ≤ b)
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (εobs : ℝ) (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ εobs ∧ If f = I r)
    (hM : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts =>
        let r := holdingSimulationObservation mr states (fun l j => floatReal (ratesF (states l) j))
          marks sr hr fuel save ts
        (T r, I r)))
    (i : ι) (t : ℝ) :
    let Fr := fun ω => observeRun (simulate realArithmetic (tapeSource ℝ) mr .direct initial sr hr
      (streamTape a b ω) fuel save cap)
    let Ff := fun ω => observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .direct initial
      start hf (floatStreamTape ρu ρe a b ω) fuel save cap)
    let β := iidStreams (directFloatStopGood mf mr htransition transition ratesF lowerF upperF CF initial
      ρu ρe start hf sr hr ε d δ η fuel cap save)ᶜ
    iidStreams.map (fun ω => (T (Fr ω), I (Fr ω))) (jointTail (t + εobs) i) ≤
        iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} + β ∧
      iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} ≤
        iidStreams.map (fun ω => (T (Fr ω), I (Fr ω))) (jointTail (t - εobs) i) + β := by
  intro Fr Ff β
  have hlaw : iidStreams.map (fun ω => (T (Fr ω), I (Fr ω))) =
      targetSimulationLaw mr transition (fun x j => floatReal (ratesF x j)) initial sr hr fuel save
        (fun r => (T r, I r)) :=
    direct_iid_simulation_law mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)) CR initial sr hr hsr fuel cap
      save a b ha hb (fun r => (T r, I r)) hM
  rw [hlaw]
  exact direct_float_iid_stop_law_bounds mf mr htransition transition ratesF lowerF upperF CF CR initial ρu ρe
    start hf sr hr ε d δ η hsr fuel cap save a b ha hb T Tf I If εobs hobs hM i t

/-- The public FloatLib NRM simulator approximates the law of the public real NRM
simulator on the same IID streams, with inactive channels and absorbing states. -/
theorem iid_float_nrm_approximates_real {σ ι : Type} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (a b : ℕ) (hb : (n + 1) * (fuel + 1) ≤ b)
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (εobs : ℝ) (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ εobs ∧ If f = I r)
    (hM : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts =>
        let r := holdingSimulationObservation mr states (fun l j => floatReal (ratesF (states l) j))
          marks sr hr fuel save ts
        (T r, I r)))
    (i : ι) (t : ℝ) :
    let Fr := fun ω => observeRun (simulate realArithmetic (tapeSource ℝ) mr .nrm initial sr hr
      (streamTape a b ω) fuel save cap)
    let Ff := fun ω => observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .nrm initial
      start hf (floatStreamTape ρu ρe a b ω) fuel save cap)
    let β := iidStreams (nrmFloatMaskedGood mf mr htransition transition ratesF lowerF upperF CF initial ρe
      start hf sr hr δ η fuel cap save)ᶜ
    iidStreams.map (fun ω => (T (Fr ω), I (Fr ω))) (jointTail (t + εobs) i) ≤
        iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} + β ∧
      iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} ≤
        iidStreams.map (fun ω => (T (Fr ω), I (Fr ω))) (jointTail (t - εobs) i) + β := by
  intro Fr Ff β
  have hlaw : iidStreams.map (fun ω => (T (Fr ω), I (Fr ω))) =
      targetSimulationLaw mr transition (fun x j => floatReal (ratesF x j)) initial sr hr fuel save
        (fun r => (T r, I r)) :=
    nrm_iid_simulation_law mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)) CR initial sr hr hsr fuel cap
      save a b hb (fun r => (T r, I r)) hM
  rw [hlaw]
  exact nrm_float_iid_masked_law_bounds mf mr htransition transition ratesF lowerF upperF CF CR initial ρu ρe
    start hf sr hr δ η hsr fuel cap save a b hb T Tf I If εobs hobs hM i t

/-- The stopped and masked certificate failure probabilities are at most those of the
positive-rate certificates. -/
theorem iid_float_stop_failure_le {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (hbv : ∀ x j, 0 ≤ floatReal (lowerF x j) ∧ floatReal (lowerF x j) ≤ floatReal (ratesF x j) ∧
      floatReal (ratesF x j) ≤ floatReal (upperF x j))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ) (ηN : Nat → ℝ)
    (fuel cap : ℕ) (save : Bool) :
    iidStreams (directFloatStopGood mf mr htransition transition ratesF lowerF upperF CF initial ρu ρe start
        hf sr hr ε d δ η fuel cap save)ᶜ ≤
      iidStreams (directFloatGood mf mr htransition transition ratesF lowerF upperF CF initial ρu ρe start
        hf sr hr ε d δ η fuel cap save)ᶜ ∧
    iidStreams (rssaFloatStopGood mf mr htransition transition ratesF lowerF upperF CF hbv initial ρu ρe
        start hf sr hr ε d δ η fuel cap save)ᶜ ≤
      iidStreams (rssaFloatGood mf mr htransition transition ratesF lowerF upperF CF hbv initial ρu ρe start
        hf sr hr ε d δ η fuel cap save)ᶜ ∧
    iidStreams (nrmFloatMaskedGood mf mr htransition transition ratesF lowerF upperF CF initial ρe start hf
        sr hr δ ηN fuel cap save)ᶜ ≤
      iidStreams (nrmFloatGood mf mr htransition transition ratesF lowerF upperF CF initial ρe start hf sr
        hr δ ηN fuel cap save)ᶜ :=
  ⟨measure_mono (compl_subset_compl.mpr (directFloatGood_subset_stop mf mr htransition transition ratesF
      lowerF upperF CF initial ρu ρe start hf sr hr ε d δ η fuel cap save)),
    measure_mono (compl_subset_compl.mpr (rssaFloatGood_subset_stop mf mr htransition transition ratesF
      lowerF upperF CF hbv initial ρu ρe start hf sr hr ε d δ η fuel cap save)),
    measure_mono (compl_subset_compl.mpr (nrmFloatGood_subset_masked mf mr htransition transition ratesF
      lowerF upperF CF initial ρe start hf sr hr δ ηN fuel cap save))⟩

end JumpProcessesLean.Proofs
