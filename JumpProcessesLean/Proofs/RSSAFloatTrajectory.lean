import JumpProcessesLean.Proofs.DirectFloatTrajectory

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def rssaFloatClock {n : Nat} (bounds : Nat → RateBounds Binary64)
    (ef : (k : Nat) → (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (k : Nat) (now : Binary64) (p : RSSAStoppingInput n) : Binary64 :=
  now + (List.ofFn (ef k p)).foldl (· + ·) 0 / sumRates binary64Arithmetic (bounds k).upper

noncomputable def rssaRealClock {n : Nat} (bounds : Nat → RateBounds Binary64)
    (k : Nat) (p : RSSAStoppingInput n) : ℝ :=
  rssaStoppingTime ((bounds k).upper.toList.map floatReal) p

/-- The full RSSA local refinement is derived for every rejected proposal and the
successful one from branch membership and the primitive numerical certificate. -/
theorem rssa_float_local_refinement {σ : Type} {n : Nat} (model : Model Binary64 σ)
    (states : Nat → σ) (marks : Nat → Nat) (rates : Nat → Array Binary64) (bounds : Nat → RateBounds Binary64)
    (hm : ∀ k, model.rates (states k) = rates k) (hb : ∀ k, model.bounds (states k) = bounds k)
    (ef uf vf : (k : Nat) → (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (source : Nat → RSSAStoppingInput n) (start : Binary64) (fuel cap : Nat) (d η : ℝ)
    (hupper : ∀ k, k ≤ fuel → ∀ a ∈ (bounds k).upper.toList.map floatReal, 0 ≤ a)
    (hB : ∀ k, k ≤ fuel → 0 < ((bounds k).upper.toList.map floatReal).sum)
    (hg : ∀ k, k ≤ fuel → (source k).1.1 + 1 ≤ cap ∧
      (∀ j, (source k).2.1 j ∈ Ioo 0 1) ∧ (∀ j, ((source k).2.2 j).1 ∈ Ioo 0 1) ∧
      (source k).2.2 ∈ proposalBranch ((rates k).toList.map floatReal)
        ((bounds k).lower.toList.map floatReal) ((bounds k).upper.toList.map floatReal)
          (source k).1.1 (marks k))
    (hc : ∀ k, k ≤ fuel → RSSAFloatCertificate (rates k) (bounds k)
      (floatTimeSchedule (rssaFloatClock bounds ef) source start k)
      (ef k (source k)) (uf k (source k)) (vf k (source k))
      (fun j => -log ((source k).2.1 j)) (fun j => ((source k).2.2 j).1)
      (fun j => ((source k).2.2 j).2) d η) :
    LocalPacketRefinement model .rssa states marks (rssaFloatClock bounds ef)
      (fun k p => proposalFloatUniforms (uf k p) (vf k p)) (fun k p => List.ofFn (ef k p))
      (rssaRealClock bounds) source start cap fuel d := by
  have href k hk us es extra := rssa_float_certificate_refines (rates k) (bounds k)
    (floatTimeSchedule (rssaFloatClock bounds ef) source start k)
    (ef k (source k)) (uf k (source k)) (vf k (source k))
    (fun j => -log ((source k).2.1 j)) (fun j => ((source k).2.2 j).1)
    (fun j => ((source k).2.2 j).2) d η (hc k hk) (hupper k hk) (hB k hk) (hg k hk).2.2.1
    (marks k) (by intro j; exact (mem_pi.mp (hg k hk).2.2.2) j (mem_univ _)) us es extra
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk us es
    have he := href k hk us es (cap - ((source k).1.1 + 1))
    rw [show (source k).1.1 + 1 + (cap - ((source k).1.1 + 1)) = cap by have := (hg k hk).1; omega] at he
    dsimp only [sampleEvent]
    rw [hm k, hb k]
    exact he.1
  · intro k hk
    have h := (hc k hk).clockValid
    rw [clockFlag, Bool.and_eq_true] at h
    exact h.1
  · intro k hk
    have h := (hc k hk).clockValid
    rw [clockFlag, Bool.and_eq_true] at h
    exact float_le_of_lt_flag _ _ (hc k hk).nowFinite h.1 h.2
  · intro k hk
    unfold rssaRealClock rssaStoppingTime exponentialClock
    exact Finset.sum_nonneg (fun j _ => (div_pos
      (neg_pos.mpr (log_neg ((hg k hk).2.1 j).1 ((hg k hk).2.1 j).2)) (hB k hk)).le)
  · intro k hk
    simpa only [floatTimeSchedule, rssaFloatClock, rssaRealClock, rssaStoppingTime, exponentialClock, Finset.sum_div] using
      (href k hk [] [] 0).2

/-- Whole native capped RSSA simulation approximation. Proposal overflow belongs
to the bad set of a probabilistic corollary, rather than being normalized away. -/
theorem rssa_float_trajectory_close {σ : Type} {n : Nat} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Nat) (rates : Nat → Array Binary64) (bounds : Nat → RateBounds Binary64)
    (hm : ∀ k, mf.rates (states k) = rates k) (hb : ∀ k, mf.bounds (states k) = bounds k)
    (hs : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (ef uf vf : (k : Nat) → (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (source : Nat → RSSAStoppingInput n) (start hf : Binary64) (sr hr ε d δ η : ℝ)
    (fuel cap : Nat) (save : Bool)
    (hupper : ∀ k, k ≤ fuel → ∀ a ∈ (bounds k).upper.toList.map floatReal, 0 ≤ a)
    (hB : ∀ k, k ≤ fuel → 0 < ((bounds k).upper.toList.map floatReal).sum)
    (hg : ∀ k, k ≤ fuel → (source k).1.1 + 1 ≤ cap ∧
      (∀ j, (source k).2.1 j ∈ Ioo 0 1) ∧ (∀ j, ((source k).2.2 j).1 ∈ Ioo 0 1) ∧
      (source k).2.2 ∈ proposalBranch ((rates k).toList.map floatReal)
        ((bounds k).lower.toList.map floatReal) ((bounds k).upper.toList.map floatReal)
          (source k).1.1 (marks k))
    (hc : ∀ k, k ≤ fuel → RSSAFloatCertificate (rates k) (bounds k)
      (floatTimeSchedule (rssaFloatClock bounds ef) source start k)
      (ef k (source k)) (uf k (source k)) (vf k (source k))
      (fun j => -log ((source k).2.1 j)) (fun j => ((source k).2.2 j).1)
      (fun j => ((source k).2.2 j).2) d η)
    (hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true) (hstart : binary64Arithmetic.lt start hf = true)
    (hhf : ExecFloat.Binary.isFinite hf = true) (hh : |floatReal hf - hr| ≤ δ)
    (h0 : |floatReal start - sr| ≤ ε) (hd : 0 ≤ d)
    (hbudget : ε + ((fuel + 1 : Nat) : ℝ) * d ≤ δ)
    (hmargin : ∀ k, k ≤ fuel → 2 * δ < |realTimeSchedule (rssaRealClock bounds) source sr (k + 1) - hr|) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .rssa (states 0) start hf
        (floatPacketTape (fun k p => proposalFloatUniforms (uf k p) (vf k p))
          (fun k p => List.ofFn (ef k p)) source 0 (fuel + 1)) fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (rssaRealClock bounds) source sr) marks 0 (fuel + 1))) := by
  exact float_packet_trajectory_close mf mr .rssa (by intro h; cases h) htransition states marks
    (rssaFloatClock bounds ef) (fun k p => proposalFloatUniforms (uf k p) (vf k p))
    (fun k p => List.ofFn (ef k p)) (rssaRealClock bounds) source start hf sr hr ε d δ fuel cap save
    (rssa_float_local_refinement mf states marks rates bounds hm hb ef uf vf source start fuel cap d η hupper hB hg hc)
    hs hvalid hstart hhf hh h0 hd hbudget hmargin

end JumpProcessesLean.Proofs
