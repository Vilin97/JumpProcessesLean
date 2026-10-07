import JumpProcessesLean.Proofs.TrajectoryCertificates

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def jointTail {ι : Type} (t : ℝ) (i : ι) : Set (ℝ × ι) := {z | t < z.1 ∧ z.2 = i}

/-- Internal measure-theoretic composition. The algorithm-specific theorems below
prove both the real law and float trace refinement from primitive input. -/
theorem trace_joint_bounds_of_law {Ω σ ι : Type} [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (μ : Measure Ω)
    (R : Ω → Except Error (TraceObservation ℝ σ)) (F : Ω → Except Error (TraceObservation Binary64 σ))
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (ν : Measure (ℝ × ι)) (hMR : Measurable (fun p => (T (R p), I (R p))))
    (hlaw : μ.map (fun p => (T (R p), I (R p))) = ν)
    (bad : Set Ω) (hbad : MeasurableSet bad) (δ ε : ℝ) (hε : 0 ≤ ε)
    (htrace : ∀ p ∉ bad, TraceClose δ (F p) (R p))
    (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ ε ∧ If f = I r) (i : ι) (t : ℝ) :
    ν (jointTail (t + ε) i) ≤ μ {p | t < Tf (F p) ∧ If (F p) = i} + μ bad ∧
      μ {p | t < Tf (F p) ∧ If (F p) = i} ≤ ν (jointTail (t - ε) i) + μ bad := by
  have h := coupled_trace_observable_bounds μ R F T Tf I If bad hbad δ ε hε htrace hobs i t
  have ht (s : ℝ) : μ {p | s < T (R p) ∧ I (R p) = i} = ν (jointTail s i) := by
    rw [← hlaw, Measure.map_apply hMR (by unfold jointTail; measurability)]
    rfl
  rw [ht (t + ε), ht (t - ε)] at h
  exact h

noncomputable def directFloatRun {σ : Type} (model : Model Binary64 σ) (initial : σ)
    (ef uf : Nat → ℝ × ℝ → Binary64) (start horizon : Binary64) (fuel cap : Nat) (save : Bool)
    (p : Fin (fuel + 1) → ℝ × ℝ) : Except Error (TraceObservation Binary64 σ) :=
  observeRun (simulate binary64Arithmetic (tapeSource Binary64) model .direct initial start horizon
    (floatPacketTape (fun k p => [uf k p]) (fun k p => [ef k p])
      (rawChronological (1 / 2, 1 / 2) p) 0 (fuel + 1)) fuel save cap)

/-- Complete native FloatLib Direct trace distribution approximation. The real
measure on the right is the marked-exponential path law, not an assumed law of
an auxiliary sampler. `bad` accounts for all failed numerical/source margins. -/
theorem direct_float_simulation_joint_tail_approx {σ ι : Type} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {n : Nat} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Fin (n + 1)) (rates : Nat → Fin (n + 1) → Binary64)
    (hm : ∀ k, mf.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, mf.transition (states k) (marks k).val = .ok (states (k + 1)))
    (hn : ∀ k j, 0 ≤ floatReal (rates k j)) (hA : ∀ k, 0 < ∑ j, floatReal (rates k j))
    (ef uf : Nat → ℝ × ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η εobs : ℝ)
    (fuel cap : Nat) (save : Bool)
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (hεobs : 0 ≤ εobs)
    (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ εobs ∧ If f = I r)
    (hM : Measurable (fun ts =>
      let r := holdingSimulationObservation mr states (fun k j => floatReal (rates k j)) marks sr hr fuel save ts
      (T r, I r)))
    (bad : Set (Fin (fuel + 1) → ℝ × ℝ)) (hbad : MeasurableSet bad)
    (hgood : ∀ p ∉ bad, DirectTrajectoryConditions mf mr htransition states (fun k => (marks k).val)
      (fun k => Array.ofFn (rates k)) hm hs ef uf (rawChronological (1 / 2, 1 / 2) p)
      start hf sr hr ε d δ η fuel cap save)
    (i : ι) (t : ℝ) :
    let μ := rawWordLaw (fun k => directPacketInputs (fun j => floatReal (rates k j)) (marks k)) (fuel + 1)
    let ν := (targetWordLaw (fun k j => floatReal (rates k j)) marks (fuel + 1)).map
      (fun ts =>
        let r := holdingSimulationObservation mr states (fun k j => floatReal (rates k j))
          marks sr hr fuel save ts
        (T r, I r))
    ν (jointTail (t + εobs) i) ≤ μ {p | t < Tf (directFloatRun mf (states 0) ef uf start hf fuel cap save p) ∧
      If (directFloatRun mf (states 0) ef uf start hf fuel cap save p) = i} + μ bad ∧
    μ {p | t < Tf (directFloatRun mf (states 0) ef uf start hf fuel cap save p) ∧
      If (directFloatRun mf (states 0) ef uf start hf fuel cap save p) = i} ≤ ν (jointTail (t - εobs) i) + μ bad := by
  dsimp only
  let rr := fun k j => floatReal (rates k j)
  let inputs := fun k => directPacketInputs (rr k) (marks k)
  let clock := directRealClock (fun k => Array.ofFn (rates k))
  let R := packetRealReplay mr states marks clock (1 / 2, 1 / 2) sr hr fuel save
  have hcomplete (k : Nat) : completedRates (rr k) = rr k := by simp only [completedRates, hA, ite_true, rr]
  have hmclock (k : Nat) : Measurable (clock k) := (measurable_exponentialClock _).comp measurable_fst
  have hclock (k : Nat) : (inputs k).map (clock k) =
      ENNReal.ofReal (completedRates (rr k) (marks k) / (∑ j, completedRates (rr k) j)) •
        expMeasure (∑ j, completedRates (rr k) j) := by
    have h := direct_packet_clock_law (rr k) (hn k) (marks k)
    have he : clock k = fun p : ℝ × ℝ => exponentialClock (∑ j, rr k j) p.1 := by
      funext p
      simp only [clock, directRealClock, Array.toList_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]
      rfl
    rw [he]
    simpa only [hcomplete] using h
  have hlaw := primitive_packet_replay_law mr states rr marks clock inputs
    (fun k => by unfold inputs directPacketInputs; infer_instance) hmclock hclock (1 / 2, 1 / 2) sr hr fuel save
    (fun k _ => hA k) (fun r => (T r, I r)) hM
  simp_rw [hcomplete] at hlaw
  have hMR : Measurable (fun p => (T (R p), I (R p))) := by
    unfold R
    simp_rw [packet_real_replay_eq_holdings mr states rr marks clock (1 / 2, 1 / 2) sr hr fuel save (fun k _ => hA k)]
    exact hM.comp (measurable_rawWordHoldings clock hmclock _)
  apply trace_joint_bounds_of_law (rawWordLaw inputs (fuel + 1)) R
    (directFloatRun mf (states 0) ef uf start hf fuel cap save) T Tf I If _ hMR hlaw bad hbad δ εobs hεobs
  · intro p hp
    exact DirectTrajectoryConditions.refines mf mr htransition states (fun k => (marks k).val)
      (fun k => Array.ofFn (rates k)) hm hs ef uf (rawChronological (1 / 2, 1 / 2) p)
      start hf sr hr ε d δ η fuel cap save (hgood p hp)
  · exact hobs

noncomputable def nrmFloatRun {σ : Type} {n : Nat} (model : Model Binary64 σ) (initial : σ)
    (rates : Nat → Fin (n + 1) → Binary64) (marks : Nat → Fin (n + 1))
    (fuel cap : Nat) (ef : NRMRawInput n (fuel + 1) → Nat → Fin (n + 1) → Binary64)
    (start horizon : Binary64) (save : Bool) (p : NRMRawInput n (fuel + 1)) :
    Except Error (TraceObservation Binary64 σ) :=
  observeRun (simulate binary64Arithmetic (tapeSource Binary64) model .nrm initial start horizon
    ⟨[], List.ofFn (ef p 0) ++ nrmFloatTape rates (ef p) marks 0 fuel⟩ fuel save cap)

/-- Complete native NRM simulation distribution bounds, with initialization and
all persistent cache errors derived from the primitive numerical conditions. -/
theorem nrm_float_simulation_joint_tail_approx {σ ι : Type} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {n : Nat} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Fin (n + 1)) (rates : Nat → Fin (n + 1) → Binary64)
    (hm : ∀ k, mf.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, mf.transition (states k) (marks k).val = .ok (states (k + 1)))
    (hpos : ∀ k j, 0 < floatReal (rates k j)) (fuel cap : Nat) (save : Bool)
    (ef : NRMRawInput n (fuel + 1) → Nat → Fin (n + 1) → Binary64)
    (start hf : Binary64) (sr hr δ εobs : ℝ) (η : Nat → ℝ)
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (hεobs : 0 ≤ εobs)
    (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ εobs ∧ If f = I r)
    (hM : Measurable (fun ts =>
      let r := holdingSimulationObservation mr states (fun k j => floatReal (rates k j)) marks sr hr fuel save ts
      (T r, I r)))
    (bad : Set (NRMRawInput n (fuel + 1))) (hbad : MeasurableSet bad)
    (hgood : ∀ p ∉ bad, NRMTrajectoryConditions mf mr htransition states marks rates (ef p)
      (nrmRawExponentials p) hm hs start hf sr hr δ η fuel cap save)
    (i : ι) (t : ℝ) :
    let μ := nrmRawPathLaw (fun k j => floatReal (rates k j)) marks (fuel + 1)
    let ν := (targetWordLaw (fun k j => floatReal (rates k j)) marks (fuel + 1)).map
      (fun ts =>
        let r := holdingSimulationObservation mr states (fun k j => floatReal (rates k j)) marks sr hr fuel save ts
        (T r, I r))
    ν (jointTail (t + εobs) i) ≤ μ {p | t < Tf (nrmFloatRun mf (states 0) rates marks fuel cap ef start hf save p) ∧
      If (nrmFloatRun mf (states 0) rates marks fuel cap ef start hf save p) = i} + μ bad ∧
    μ {p | t < Tf (nrmFloatRun mf (states 0) rates marks fuel cap ef start hf save p) ∧
      If (nrmFloatRun mf (states 0) rates marks fuel cap ef start hf save p) = i} ≤ ν (jointTail (t - εobs) i) + μ bad := by
  dsimp only
  let R := nrmRealReplay mr states rates marks sr hr fuel save
  have hlaw := primitive_nrm_replay_law mr states rates marks hpos sr hr fuel save (fun r => (T r, I r)) hM
  have hMR : Measurable (fun p => (T (R p), I (R p))) := by
    unfold R
    simp_rw [nrm_real_replay_eq_holdings mr states rates marks hpos sr hr fuel save]
    exact hM.comp ((measurable_nrmRawHistory _ _ _).fst)
  apply trace_joint_bounds_of_law (nrmRawPathLaw (fun k j => floatReal (rates k j)) marks (fuel + 1))
    R (nrmFloatRun mf (states 0) rates marks fuel cap ef start hf save) T Tf I If _ hMR hlaw
    bad hbad δ εobs hεobs
  · intro p hp
    exact NRMTrajectoryConditions.refines mf mr htransition states marks rates (ef p) (nrmRawExponentials p)
      hm hs start hf sr hr δ η fuel cap save (hgood p hp)
  · exact hobs

noncomputable def rssaFloatRun {σ : Type} {n : Nat} (model : Model Binary64 σ) (initial : σ)
    (ef uf vf : (k : Nat) → (p : RSSAStoppingInput (n + 1)) → Fin (p.1.1 + 1) → Binary64)
    (start horizon : Binary64) (fuel cap : Nat) (save : Bool)
    (p : Fin (fuel + 1) → RSSAStoppingInput (n + 1)) : Except Error (TraceObservation Binary64 σ) :=
  observeRun (simulate binary64Arithmetic (tapeSource Binary64) model .rssa initial start horizon
    (floatPacketTape (fun k p => proposalFloatUniforms (uf k p) (vf k p)) (fun k p => List.ofFn (ef k p))
      (rawChronological ⟨(0, 0), (fun _ => 1 / 2, fun _ => (1 / 2, 1 / 2))⟩ p) 0 (fuel + 1)) fuel save cap)

/-- Whole capped FloatLib RSSA trace distribution bounds. Rejected clock errors,
source errors and proposal exhaustion are included in the certificate bad mass. -/
theorem rssa_float_simulation_joint_tail_approx {σ ι : Type} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {n : Nat} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Fin (n + 1)) (rates lower upper : Nat → Fin (n + 1) → Binary64)
    (hm : ∀ k, mf.rates (states k) = Array.ofFn (rates k))
    (hb : ∀ k, mf.bounds (states k) = ⟨Array.ofFn (lower k), Array.ofFn (upper k)⟩)
    (hs : ∀ k, mf.transition (states k) (marks k).val = .ok (states (k + 1)))
    (hA : ∀ k, 0 < ∑ j, floatReal (rates k j))
    (hbounds : ∀ k j, 0 ≤ floatReal (lower k j) ∧ floatReal (lower k j) ≤ floatReal (rates k j) ∧
      floatReal (rates k j) ≤ floatReal (upper k j))
    (ef uf vf : (k : Nat) → (p : RSSAStoppingInput (n + 1)) → Fin (p.1.1 + 1) → Binary64)
    (start hf : Binary64) (sr hr ε d δ η εobs : ℝ) (fuel cap : Nat) (save : Bool)
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (hεobs : 0 ≤ εobs)
    (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ εobs ∧ If f = I r)
    (hM : Measurable (fun ts =>
      let r := holdingSimulationObservation mr states (fun k j => floatReal (rates k j)) marks sr hr fuel save ts
      (T r, I r)))
    (bad : Set (Fin (fuel + 1) → RSSAStoppingInput (n + 1))) (hbad : MeasurableSet bad)
    (hgood : ∀ p ∉ bad, RSSATrajectoryConditions mf mr htransition states (fun k => (marks k).val)
      (fun k => Array.ofFn (rates k)) (fun k => ⟨Array.ofFn (lower k), Array.ofFn (upper k)⟩) hm hb hs
      ef uf vf (rawChronological ⟨(0, 0), (fun _ => 1 / 2, fun _ => (1 / 2, 1 / 2))⟩ p)
      start hf sr hr ε d δ η fuel cap save)
    (i : ι) (t : ℝ) :
    let μ := rawWordLaw (fun k => rssaPacketInputs (fun j => floatReal (rates k j))
      (fun j => floatReal (lower k j)) (fun j => floatReal (upper k j)) (marks k)) (fuel + 1)
    let ν := (targetWordLaw (fun k j => floatReal (rates k j)) marks (fuel + 1)).map
      (fun ts =>
        let r := holdingSimulationObservation mr states (fun k j => floatReal (rates k j)) marks sr hr fuel save ts
        (T r, I r))
    ν (jointTail (t + εobs) i) ≤ μ {p | t < Tf (rssaFloatRun mf (states 0) ef uf vf start hf fuel cap save p) ∧
      If (rssaFloatRun mf (states 0) ef uf vf start hf fuel cap save p) = i} + μ bad ∧
    μ {p | t < Tf (rssaFloatRun mf (states 0) ef uf vf start hf fuel cap save p) ∧
      If (rssaFloatRun mf (states 0) ef uf vf start hf fuel cap save p) = i} ≤ ν (jointTail (t - εobs) i) + μ bad := by
  dsimp only
  let rr := fun k j => floatReal (rates k j)
  let lo := fun k j => floatReal (lower k j)
  let up := fun k j => floatReal (upper k j)
  let inputs := fun k => rssaPacketInputs (rr k) (lo k) (up k) (marks k)
  let bounds : Nat → RateBounds Binary64 := fun k => ⟨Array.ofFn (lower k), Array.ofFn (upper k)⟩
  let clock : Nat → RSSAStoppingInput (n + 1) → ℝ := rssaRealClock bounds
  let fallback : RSSAStoppingInput (n + 1) := ⟨(0, 0), (fun _ => 1 / 2, fun _ => (1 / 2, 1 / 2))⟩
  let R := packetRealReplay mr states marks clock fallback sr hr fuel save
  have hcomplete (k : Nat) : completedRates (rr k) = rr k := by simp only [completedRates, hA, ite_true, rr]
  have hupcomplete (k : Nat) : completedUpper (rr k) (up k) = up k := by simp only [completedUpper, hA, ite_true, rr]
  have hmclock (k : Nat) : Measurable (clock k) := measurable_rssaStoppingTime _
  have hclock (k : Nat) : (inputs k).map (clock k) =
      ENNReal.ofReal (completedRates (rr k) (marks k) / (∑ j, completedRates (rr k) j)) •
        expMeasure (∑ j, completedRates (rr k) j) := by
    have h := rssa_packet_clock_law (rr k) (lo k) (up k) (hbounds k) (marks k)
    have he : clock k = rssaStoppingTime (List.ofFn (up k)) := by
      funext p
      simp only [clock, rssaRealClock, bounds, Array.toList_ofFn, List.map_ofFn, Function.comp_def]
      rfl
    rw [he]
    simpa only [hupcomplete] using h
  have hlaw := primitive_packet_replay_law mr states rr marks clock inputs
    (fun k => rssa_packet_finite _ _ _ (hbounds k) _) hmclock hclock fallback sr hr fuel save
    (fun k _ => hA k) (fun r => (T r, I r)) hM
  simp_rw [hcomplete] at hlaw
  have hMR : Measurable (fun p => (T (R p), I (R p))) := by
    unfold R
    simp_rw [packet_real_replay_eq_holdings mr states rr marks clock fallback sr hr fuel save (fun k _ => hA k)]
    exact hM.comp (measurable_rawWordHoldings clock hmclock _)
  apply trace_joint_bounds_of_law (rawWordLaw inputs (fuel + 1)) R
    (rssaFloatRun mf (states 0) ef uf vf start hf fuel cap save) T Tf I If _ hMR hlaw bad hbad δ εobs hεobs
  · intro p hp
    exact RSSATrajectoryConditions.refines mf mr htransition states (fun k => (marks k).val)
      (fun k => Array.ofFn (rates k)) bounds hm hb hs ef uf vf (rawChronological fallback p)
      start hf sr hr ε d δ η fuel cap save (hgood p hp)
  · exact hobs

end JumpProcessesLean.Proofs
