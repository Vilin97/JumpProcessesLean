import JumpProcessesLean.Proofs.PrimitiveReplayLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- Primitive inputs, finite arithmetic, branch margins and propagated budget
conditions. It contains no assumed sampler law or output agreement. -/
structure DirectTrajectoryConditions {σ : Type}
    (mf : Model Binary64 σ)
    (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ)
    (marks : Nat → Nat)
    (rates : Nat → Array Binary64)
    (hm : ∀ k, mf.rates (states k) = rates k)
    (hs : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (ef uf : Nat → ℝ × ℝ → Binary64)
    (source : Nat → ℝ × ℝ)
    (start hf : Binary64)
    (sr hr ε d δ η : ℝ)
    (fuel cap : Nat)
    (save : Bool) : Prop where
  hA : ∀ k, k ≤ fuel → 0 < ((rates k).toList.map floatReal).sum
  hg : ∀ k, k ≤ fuel → (source k).1 ∈ Ioo 0 1 ∧ (source k).2 ∈ Ioo 0 1 ∧
      selection ((rates k).toList.map floatReal) (source k).2 = some (marks k)
  hc : ∀ k, k ≤ fuel → DirectStepCertificate (rates k)
      (floatTimeSchedule (directFloatClock rates ef) source start k)
      (ef k (source k)) (uf k (source k)) (source k).2 (-log (source k).1) d η
  hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true
  hstart : binary64Arithmetic.lt start hf = true
  hhf : ExecFloat.Binary.isFinite hf = true
  hh : |floatReal hf - hr| ≤ δ
  h0 : |floatReal start - sr| ≤ ε
  hd : 0 ≤ d
  hbudget : ε + ((fuel + 1 : Nat) : ℝ) * d ≤ δ
  hmargin : ∀ k, k ≤ fuel → 2 * δ < |realTimeSchedule (directRealClock rates) source sr (k + 1) - hr|

/-- The numeric certificate derives the complete native simulation refinement. -/
theorem DirectTrajectoryConditions.refines {σ : Type}
    (mf : Model Binary64 σ)
    (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ)
    (marks : Nat → Nat)
    (rates : Nat → Array Binary64)
    (hm : ∀ k, mf.rates (states k) = rates k)
    (hs : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (ef uf : Nat → ℝ × ℝ → Binary64)
    (source : Nat → ℝ × ℝ)
    (start hf : Binary64)
    (sr hr ε d δ η : ℝ)
    (fuel cap : Nat)
    (save : Bool)
    (C : DirectTrajectoryConditions mf mr htransition states marks rates hm hs ef uf source start hf sr hr ε d δ η fuel cap save) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .direct (states 0) start hf
        (floatPacketTape (fun k p => [uf k p]) (fun k p => [ef k p]) source 0 (fuel + 1)) fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (directRealClock rates) source sr) marks 0 (fuel + 1))) := by
  exact direct_float_trajectory_close mf mr htransition states marks rates hm hs ef uf source start hf sr hr ε d δ η fuel cap save
    C.hA C.hg C.hc C.hvalid C.hstart C.hhf C.hh C.h0 C.hd C.hbudget C.hmargin

/-- Primitive inputs, finite arithmetic, branch margins and propagated budget
conditions. It contains no assumed sampler law or output agreement. -/
structure RSSATrajectoryConditions {σ : Type}
    {n : Nat}
    (mf : Model Binary64 σ)
    (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ)
    (marks : Nat → Nat)
    (rates : Nat → Array Binary64)
    (bounds : Nat → RateBounds Binary64)
    (hm : ∀ k, mf.rates (states k) = rates k)
    (hb : ∀ k, mf.bounds (states k) = bounds k)
    (hs : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (ef uf vf : (k : Nat) → (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (source : Nat → RSSAStoppingInput n)
    (start hf : Binary64)
    (sr hr ε d δ η : ℝ)
    (fuel cap : Nat)
    (save : Bool) : Prop where
  hupper : ∀ k, k ≤ fuel → ∀ a ∈ (bounds k).upper.toList.map floatReal, 0 ≤ a
  hB : ∀ k, k ≤ fuel → 0 < ((bounds k).upper.toList.map floatReal).sum
  hg : ∀ k, k ≤ fuel → (source k).1.1 + 1 ≤ cap ∧
      (∀ j, (source k).2.1 j ∈ Ioo 0 1) ∧ (∀ j, ((source k).2.2 j).1 ∈ Ioo 0 1) ∧
      (source k).2.2 ∈ proposalBranch ((rates k).toList.map floatReal)
        ((bounds k).lower.toList.map floatReal) ((bounds k).upper.toList.map floatReal)
          (source k).1.1 (marks k)
  hc : ∀ k, k ≤ fuel → RSSAFloatCertificate (rates k) (bounds k)
      (floatTimeSchedule (rssaFloatClock bounds ef) source start k)
      (ef k (source k)) (uf k (source k)) (vf k (source k))
      (fun j => -log ((source k).2.1 j)) (fun j => ((source k).2.2 j).1)
      (fun j => ((source k).2.2 j).2) d η
  hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true
  hstart : binary64Arithmetic.lt start hf = true
  hhf : ExecFloat.Binary.isFinite hf = true
  hh : |floatReal hf - hr| ≤ δ
  h0 : |floatReal start - sr| ≤ ε
  hd : 0 ≤ d
  hbudget : ε + ((fuel + 1 : Nat) : ℝ) * d ≤ δ
  hmargin : ∀ k, k ≤ fuel → 2 * δ < |realTimeSchedule (rssaRealClock bounds) source sr (k + 1) - hr|

/-- The numeric certificate derives the complete native simulation refinement. -/
theorem RSSATrajectoryConditions.refines {σ : Type}
    {n : Nat}
    (mf : Model Binary64 σ)
    (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ)
    (marks : Nat → Nat)
    (rates : Nat → Array Binary64)
    (bounds : Nat → RateBounds Binary64)
    (hm : ∀ k, mf.rates (states k) = rates k)
    (hb : ∀ k, mf.bounds (states k) = bounds k)
    (hs : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (ef uf vf : (k : Nat) → (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (source : Nat → RSSAStoppingInput n)
    (start hf : Binary64)
    (sr hr ε d δ η : ℝ)
    (fuel cap : Nat)
    (save : Bool)
    (C : RSSATrajectoryConditions mf mr htransition states marks rates bounds hm hb hs ef uf vf source start hf sr hr ε d δ η fuel cap save) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .rssa (states 0) start hf
        (floatPacketTape (fun k p => proposalFloatUniforms (uf k p) (vf k p))
          (fun k p => List.ofFn (ef k p)) source 0 (fuel + 1)) fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (rssaRealClock bounds) source sr) marks 0 (fuel + 1))) := by
  exact rssa_float_trajectory_close mf mr htransition states marks rates bounds hm hb hs ef uf vf source start hf sr hr ε d δ η fuel cap save
    C.hupper C.hB C.hg C.hc C.hvalid C.hstart C.hhf C.hh C.h0 C.hd C.hbudget C.hmargin

/-- Primitive inputs, finite arithmetic, branch margins and propagated budget
conditions. It contains no assumed sampler law or output agreement. -/
structure NRMTrajectoryConditions {σ : Type}
    {n : Nat}
    (mf : Model Binary64 σ)
    (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ)
    (marks : Nat → Fin (n + 1))
    (rates e : Nat → Fin (n + 1) → Binary64)
    (er : Nat → Fin (n + 1) → ℝ)
    (hm : ∀ k, mf.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, mf.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start hf : Binary64)
    (sr hr δ : ℝ)
    (η : Nat → ℝ)
    (fuel cap : Nat)
    (save : Bool) : Prop where
  hp : ∀ l j, binary64Arithmetic.lt 0 (rates l j) = true
  hv : ∀ l j, validRate binary64Arithmetic (rates l j) = true
  hi : NRMInitConditions (rates 0) (e 0) (er 0) start sr (η 0)
  hc : ∀ k, k < fuel → NRMUpdateConditions (rates k) (rates (k + 1))
      (nrmFloatClocks rates e marks start k) (e (k + 1)) (er (k + 1))
      (nrmFloatTimes rates e marks start (k + 1)) (η k) (η k) (η (k + 1)) (marks k)
  hcacheFinite : ∀ k, k ≤ fuel → ∀ j, ExecFloat.Binary.isFinite (nrmFloatClocks rates e marks start k j) = true
  hgap : ∀ k, k ≤ fuel → ∀ j, j ≠ marks k →
      nrmRealClocks rates er marks sr k (marks k) + 2 * η k < nrmRealClocks rates er marks sr k j
  hinc : ∀ k, k ≤ fuel → binary64Arithmetic.le (nrmFloatTimes rates e marks start k)
      (nrmFloatTimes rates e marks start (k + 1)) = true
  hrinc : ∀ k, k ≤ fuel → nrmRealTimes rates er marks sr k ≤ nrmRealTimes rates er marks sr (k + 1)
  hbudget : ∀ k, k ≤ fuel → η k ≤ δ
  hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true
  hstart : binary64Arithmetic.lt start hf = true
  hhf : ExecFloat.Binary.isFinite hf = true
  hh : |floatReal hf - hr| ≤ δ
  h0 : |floatReal start - sr| ≤ δ
  hmargin : ∀ k, k ≤ fuel → 2 * δ < |nrmRealTimes rates er marks sr (k + 1) - hr|

/-- The numeric certificate derives the complete native simulation refinement. -/
theorem NRMTrajectoryConditions.refines {σ : Type}
    {n : Nat}
    (mf : Model Binary64 σ)
    (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ)
    (marks : Nat → Fin (n + 1))
    (rates e : Nat → Fin (n + 1) → Binary64)
    (er : Nat → Fin (n + 1) → ℝ)
    (hm : ∀ k, mf.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, mf.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start hf : Binary64)
    (sr hr δ : ℝ)
    (η : Nat → ℝ)
    (fuel cap : Nat)
    (save : Bool)
    (C : NRMTrajectoryConditions mf mr htransition states marks rates e er hm hs start hf sr hr δ η fuel cap save) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .nrm (states 0) start hf
        ⟨[], List.ofFn (e 0) ++ nrmFloatTape rates e marks 0 fuel⟩ fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (nrmRealTimes rates er marks sr) (fun k => (marks k).val) 0 (fuel + 1))) := by
  exact nrm_float_trajectory_close mf mr htransition states marks rates e er hm hs start hf sr hr δ η fuel cap save
    C.hp C.hv C.hi C.hc C.hcacheFinite C.hgap C.hinc C.hrinc C.hbudget C.hvalid C.hstart C.hhf C.hh C.h0 C.hmargin

end JumpProcessesLean.Proofs
