import JumpProcessesLean.Proofs.FloatPacketTrajectory

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma float_le_of_lt_flag (a b : Binary64) (ha : ExecFloat.Binary.isFinite a = true)
    (hb : ExecFloat.Binary.isFinite b = true) (h : binary64Arithmetic.lt a b = true) :
    binary64Arithmetic.le a b = true := by
  have hf : a < b := of_decide_eq_true h
  have hr := (float_lt_real a b ha hb).mp hf
  exact decide_eq_true ((float_le_real a b ha hb).mpr hr.le)

noncomputable def directFloatClock (rates : Nat → Array Binary64)
    (ef : Nat → ℝ × ℝ → Binary64) (k : Nat) (now : Binary64) (p : ℝ × ℝ) : Binary64 :=
  now + ef k p / sumRates binary64Arithmetic (rates k)

noncomputable def directRealClock (rates : Nat → Array Binary64) (k : Nat) (p : ℝ × ℝ) : ℝ :=
  exponentialClock ((rates k).toList.map floatReal).sum p.1

/-- Full native Direct local refinement, constructed solely from the input
certificate, primitive uniform ranges and CDF branch membership. -/
theorem direct_float_local_refinement {σ : Type} (model : Model Binary64 σ)
    (states : Nat → σ) (marks : Nat → Nat) (rates : Nat → Array Binary64)
    (hm : ∀ k, model.rates (states k) = rates k)
    (ef uf : Nat → ℝ × ℝ → Binary64) (source : Nat → ℝ × ℝ)
    (start : Binary64) (fuel cap : Nat) (d η : ℝ)
    (hA : ∀ k, k ≤ fuel → 0 < ((rates k).toList.map floatReal).sum)
    (hg : ∀ k, k ≤ fuel → (source k).1 ∈ Ioo 0 1 ∧ (source k).2 ∈ Ioo 0 1 ∧
      selection ((rates k).toList.map floatReal) (source k).2 = some (marks k))
    (hc : ∀ k, k ≤ fuel → DirectStepCertificate (rates k)
      (floatTimeSchedule (directFloatClock rates ef) source start k)
      (ef k (source k)) (uf k (source k)) (source k).2 (-log (source k).1) d η) :
    LocalPacketRefinement model .direct states marks (directFloatClock rates ef)
      (fun k p => [uf k p]) (fun k p => [ef k p]) (directRealClock rates) source start cap fuel d := by
  have href k hk := direct_float_step_refines (rates k)
    (floatTimeSchedule (directFloatClock rates ef) source start k) (ef k (source k)) (uf k (source k))
    (source k).2 (-log (source k).1) d η (hc k hk) (hA k hk) (hg k hk).2.1 (marks k) (hg k hk).2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk us es
    dsimp only [sampleEvent]
    rw [hm k]
    simpa only [List.singleton_append, floatTimeSchedule, directFloatClock] using (href k hk us es).1
  · intro k hk
    have h := (hc k hk).clockValid
    rw [clockFlag, Bool.and_eq_true] at h
    exact h.1
  · intro k hk
    have h := (hc k hk).clockValid
    rw [clockFlag, Bool.and_eq_true] at h
    exact float_le_of_lt_flag _ _ (hc k hk).nowFinite h.1 h.2
  · intro k hk
    exact (div_pos (neg_pos.mpr (log_neg (hg k hk).1.1 (hg k hk).1.2)) (hA k hk)).le
  · intro k hk
    exact (href k hk [] []).2

/-- End-to-end FloatLib Direct trace approximation. Local numerical/source
budgets are accumulated by induction through the actual public simulator. -/
theorem direct_float_trajectory_close {σ : Type} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Nat) (rates : Nat → Array Binary64)
    (hm : ∀ k, mf.rates (states k) = rates k)
    (hs : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (ef uf : Nat → ℝ × ℝ → Binary64) (source : Nat → ℝ × ℝ)
    (start hf : Binary64) (sr hr ε d δ η : ℝ) (fuel cap : Nat) (save : Bool)
    (hA : ∀ k, k ≤ fuel → 0 < ((rates k).toList.map floatReal).sum)
    (hg : ∀ k, k ≤ fuel → (source k).1 ∈ Ioo 0 1 ∧ (source k).2 ∈ Ioo 0 1 ∧
      selection ((rates k).toList.map floatReal) (source k).2 = some (marks k))
    (hc : ∀ k, k ≤ fuel → DirectStepCertificate (rates k)
      (floatTimeSchedule (directFloatClock rates ef) source start k)
      (ef k (source k)) (uf k (source k)) (source k).2 (-log (source k).1) d η)
    (hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true) (hstart : binary64Arithmetic.lt start hf = true)
    (hhf : ExecFloat.Binary.isFinite hf = true) (hh : |floatReal hf - hr| ≤ δ)
    (h0 : |floatReal start - sr| ≤ ε) (hd : 0 ≤ d)
    (hbudget : ε + ((fuel + 1 : Nat) : ℝ) * d ≤ δ)
    (hmargin : ∀ k, k ≤ fuel → 2 * δ < |realTimeSchedule (directRealClock rates) source sr (k + 1) - hr|) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .direct (states 0) start hf
        (floatPacketTape (fun k p => [uf k p]) (fun k p => [ef k p]) source 0 (fuel + 1)) fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (directRealClock rates) source sr) marks 0 (fuel + 1))) := by
  exact float_packet_trajectory_close mf mr .direct (by intro h; cases h) htransition states marks
    (directFloatClock rates ef) (fun k p => [uf k p]) (fun k p => [ef k p]) (directRealClock rates)
    source start hf sr hr ε d δ fuel cap save
    (direct_float_local_refinement mf states marks rates hm ef uf source start fuel cap d η hA hg hc)
    hs hvalid hstart hhf hh h0 hd hbudget hmargin

end JumpProcessesLean.Proofs
