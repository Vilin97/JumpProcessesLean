import JumpProcessesLean.Proofs.FloatScheduleAbsorb

/-!
# Direct and RSSA float certificates that allow absorbing states

A *stop index* `m ≤ fuel + 1` splits the certified schedule. Every step `k < m` carries
the usual one-event numerical certificate. If `m ≤ fuel`, step `m` is an absorbing state
and the native FloatLib sampler must report it (input-only flags on the float rates at
that state). When `m = fuel + 1` the event budget is exhausted before any absorption.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- The native FloatLib Direct call reports an absorbing state without drawing. -/
lemma direct_float_absorbing (rates : Array Binary64) (now : Binary64) (rng : Tape Binary64)
    (hr : ∀ a ∈ rates.toList, validRate binary64Arithmetic a = true)
    (hn : ExecFloat.Binary.isFinite now = true)
    (hT : binary64Arithmetic.finite (sumRates binary64Arithmetic rates) = true)
    (hZ : binary64Arithmetic.lt binary64Arithmetic.zero (sumRates binary64Arithmetic rates) = false) :
    direct binary64Arithmetic (tapeSource Binary64) rates now rng = .ok (none, rng) := by
  have hc : checkRates binary64Arithmetic rates = .ok () := checkRatesAux_valid _ _ hr 0
  unfold direct
  rw [hc]
  simp only [Bind.bind, Except.bind]
  rw [show binary64Arithmetic.finite now = true from hn, hT, hZ]
  rfl

/-- The native FloatLib RSSA call reports an absorbing state without drawing. -/
lemma rssa_float_absorbing (rates : Array Binary64) (bounds : RateBounds Binary64) (now : Binary64)
    (rng : Tape Binary64) (cap : Nat)
    (hb : checkBounds binary64Arithmetic rates bounds = .ok ())
    (hn : ExecFloat.Binary.isFinite now = true)
    (hT : ExecFloat.Binary.isFinite (sumRates binary64Arithmetic bounds.upper) = true)
    (ha : rates.any (binary64Arithmetic.lt binary64Arithmetic.zero) = false) :
    rssa binary64Arithmetic (tapeSource Binary64) rates bounds now rng cap = .ok (none, rng) := by
  unfold rssa
  rw [hb]
  simp only [Bind.bind, Except.bind]
  rw [show binary64Arithmetic.finite now = true from hn,
    show binary64Arithmetic.finite (sumRates binary64Arithmetic bounds.upper) = true from hT, ha]
  rfl

/-! ### Direct -/

/-- Direct numerical certificate with a stop index `m`. -/
structure DirectStopConditions {σ : Type}
    (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Nat) (rates : Nat → Array Binary64)
    (hm : ∀ k, mf.rates (states k) = rates k)
    (hs : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (ef uf : Nat → ℝ × ℝ → Binary64) (source : Nat → ℝ × ℝ)
    (start hf : Binary64) (sr hr ε d δ η : ℝ) (fuel cap m : Nat) (save : Bool) : Prop where
  stop : m ≤ fuel + 1
  hA : ∀ k, k < m → 0 < ((rates k).toList.map floatReal).sum
  hg : ∀ k, k < m → (source k).1 ∈ Ioo 0 1 ∧ (source k).2 ∈ Ioo 0 1 ∧
      selection ((rates k).toList.map floatReal) (source k).2 = some (marks k)
  hc : ∀ k, k < m → DirectStepCertificate (rates k)
      (floatTimeSchedule (directFloatClock rates ef) source start k)
      (ef k (source k)) (uf k (source k)) (source k).2 (-log (source k).1) d η
  absorbValid : m ≤ fuel → ∀ a ∈ (rates m).toList, validRate binary64Arithmetic a = true
  absorbFinite : m ≤ fuel → binary64Arithmetic.finite (sumRates binary64Arithmetic (rates m)) = true
  absorbZero : m ≤ fuel →
    binary64Arithmetic.lt binary64Arithmetic.zero (sumRates binary64Arithmetic (rates m)) = false
  hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true
  hstart : binary64Arithmetic.lt start hf = true
  hhf : ExecFloat.Binary.isFinite hf = true
  hh : |floatReal hf - hr| ≤ δ
  h0 : |floatReal start - sr| ≤ ε
  hd : 0 ≤ d
  hbudget : ε + ((fuel + 1 : Nat) : ℝ) * d ≤ δ
  hmargin : ∀ k, k < m → 2 * δ < |realTimeSchedule (directRealClock rates) source sr (k + 1) - hr|

lemma floatTimeSchedule_finite {γ : Type} (clock : Nat → Binary64 → γ → Binary64) (source : Nat → γ)
    (start : Binary64) (m : Nat) (hstart : ExecFloat.Binary.isFinite start = true)
    (hfin : ∀ k, k < m → ExecFloat.Binary.isFinite (floatTimeSchedule clock source start (k + 1)) = true) :
    ExecFloat.Binary.isFinite (floatTimeSchedule clock source start m) = true := by
  cases m with
  | zero => exact hstart
  | succ m => exact hfin m (by omega)

lemma start_finite_of_valid (start hf : Binary64)
    (h : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true) : ExecFloat.Binary.isFinite start = true := by
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- FloatLib Direct trajectory refinement through the actual public driver, stopping at
the first absorbing state or at the event budget. -/
theorem direct_float_trajectory_close_stop {σ : Type} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Nat) (rates : Nat → Array Binary64)
    (hm : ∀ k, mf.rates (states k) = rates k)
    (hs : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (ef uf : Nat → ℝ × ℝ → Binary64) (source : Nat → ℝ × ℝ) (tail : Tape Binary64)
    (start hf : Binary64) (sr hr ε d δ η : ℝ) (fuel cap m : Nat) (save : Bool)
    (C : DirectStopConditions mf mr htransition states marks rates hm hs ef uf source start hf sr hr ε d δ η
      fuel cap m save) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .direct (states 0) start hf
        (floatPacketTapeFrom (fun k p => [uf k p]) (fun k p => [ef k p]) source tail 0 (fuel + 1))
          fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (directRealClock rates) source sr) marks 0 m)) := by
  have href k (hk : k < m) := direct_float_step_refines (rates k)
    (floatTimeSchedule (directFloatClock rates ef) source start k) (ef k (source k)) (uf k (source k))
    (source k).2 (-log (source k).1) d η (C.hc k hk) (C.hA k hk) (C.hg k hk).2.1 (marks k) (C.hg k hk).2.2
  have hfin : ∀ k, k < m → ExecFloat.Binary.isFinite
      (floatTimeSchedule (directFloatClock rates ef) source start (k + 1)) = true := by
    intro k hk
    have h := (C.hc k hk).clockValid
    rw [clockFlag, Bool.and_eq_true] at h
    exact h.1
  by_cases hstop : m ≤ fuel
  · apply float_packet_trajectory_close_absorb mf mr .direct (by intro h; cases h) htransition states marks
      (directFloatClock rates ef) (fun k p => [uf k p]) (fun k p => [ef k p]) (directRealClock rates)
      source tail start hf sr hr ε d δ fuel cap m hstop save
    · intro k hk us es
      dsimp only [sampleEvent]
      rw [hm k]
      simpa only [List.singleton_append, floatTimeSchedule, directFloatClock] using (href k hk us es).1
    · exact hfin
    · intro k hk
      have h := (C.hc k hk).clockValid
      rw [clockFlag, Bool.and_eq_true] at h
      exact float_le_of_lt_flag _ _ (C.hc k hk).nowFinite h.1 h.2
    · intro k hk
      exact (div_pos (neg_pos.mpr (log_neg (C.hg k hk).1.1 (C.hg k hk).1.2)) (C.hA k hk)).le
    · intro k hk
      exact (href k hk [] []).2
    · intro rng
      dsimp only [sampleEvent]
      rw [hm m]
      exact direct_float_absorbing (rates m) _ rng (C.absorbValid hstop)
        (floatTimeSchedule_finite _ _ _ m (start_finite_of_valid start hf C.hvalid) hfin)
        (C.absorbFinite hstop) (C.absorbZero hstop)
    · exact fun k _ => hs k
    · exact C.hvalid
    · exact C.hstart
    · exact C.hhf
    · exact C.hh
    · exact C.h0
    · exact C.hd
    · exact C.hbudget
    · exact C.hmargin
  · have hm' : m = fuel + 1 := le_antisymm C.stop (by omega)
    subst hm'
    exact float_packet_trajectory_close_from mf mr .direct (by intro h; cases h) htransition states marks
      (directFloatClock rates ef) (fun k p => [uf k p]) (fun k p => [ef k p]) (directRealClock rates)
      source tail start hf sr hr ε d δ fuel cap save
      (direct_float_local_refinement mf states marks rates hm ef uf source start fuel cap d η
        (fun k hk => C.hA k (by omega)) (fun k hk => C.hg k (by omega)) (fun k hk => C.hc k (by omega)))
      hs C.hvalid C.hstart C.hhf C.hh C.h0 C.hd C.hbudget (fun k hk => C.hmargin k (by omega))

/-! ### RSSA -/

/-- Capped RSSA numerical certificate with a stop index `m`. -/
structure RSSAStopConditions {σ : Type} {n : Nat}
    (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Nat) (rates : Nat → Array Binary64)
    (bounds : Nat → RateBounds Binary64)
    (hm : ∀ k, mf.rates (states k) = rates k) (hb : ∀ k, mf.bounds (states k) = bounds k)
    (hs : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (ef uf vf : (k : Nat) → (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (source : Nat → RSSAStoppingInput n) (start hf : Binary64) (sr hr ε d δ η : ℝ)
    (fuel cap m : Nat) (save : Bool) : Prop where
  stop : m ≤ fuel + 1
  hupper : ∀ k, k < m → ∀ a ∈ (bounds k).upper.toList.map floatReal, 0 ≤ a
  hB : ∀ k, k < m → 0 < ((bounds k).upper.toList.map floatReal).sum
  hg : ∀ k, k < m → (source k).1.1 + 1 ≤ cap ∧
      (∀ j, (source k).2.1 j ∈ Ioo 0 1) ∧ (∀ j, ((source k).2.2 j).1 ∈ Ioo 0 1) ∧
      (source k).2.2 ∈ proposalBranch ((rates k).toList.map floatReal)
        ((bounds k).lower.toList.map floatReal) ((bounds k).upper.toList.map floatReal)
          (source k).1.1 (marks k)
  hc : ∀ k, k < m → RSSAFloatCertificate (rates k) (bounds k)
      (floatTimeSchedule (rssaFloatClock bounds ef) source start k)
      (ef k (source k)) (uf k (source k)) (vf k (source k))
      (fun j => -log ((source k).2.1 j)) (fun j => ((source k).2.2 j).1)
      (fun j => ((source k).2.2 j).2) d η
  absorbBounds : m ≤ fuel → checkBounds binary64Arithmetic (rates m) (bounds m) = .ok ()
  absorbFinite : m ≤ fuel →
    ExecFloat.Binary.isFinite (sumRates binary64Arithmetic (bounds m).upper) = true
  absorbInactive : m ≤ fuel → (rates m).any (binary64Arithmetic.lt binary64Arithmetic.zero) = false
  hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true
  hstart : binary64Arithmetic.lt start hf = true
  hhf : ExecFloat.Binary.isFinite hf = true
  hh : |floatReal hf - hr| ≤ δ
  h0 : |floatReal start - sr| ≤ ε
  hd : 0 ≤ d
  hbudget : ε + ((fuel + 1 : Nat) : ℝ) * d ≤ δ
  hmargin : ∀ k, k < m → 2 * δ < |realTimeSchedule (rssaRealClock bounds) source sr (k + 1) - hr|

/-- FloatLib capped RSSA trajectory refinement through the actual public driver,
stopping at the first absorbing state or at the event budget. -/
theorem rssa_float_trajectory_close_stop {σ : Type} {n : Nat} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Nat) (rates : Nat → Array Binary64)
    (bounds : Nat → RateBounds Binary64)
    (hm : ∀ k, mf.rates (states k) = rates k) (hb : ∀ k, mf.bounds (states k) = bounds k)
    (hs : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (ef uf vf : (k : Nat) → (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (source : Nat → RSSAStoppingInput n) (tail : Tape Binary64) (start hf : Binary64)
    (sr hr ε d δ η : ℝ) (fuel cap m : Nat) (save : Bool)
    (C : RSSAStopConditions mf mr htransition states marks rates bounds hm hb hs ef uf vf source start hf
      sr hr ε d δ η fuel cap m save) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .rssa (states 0) start hf
        (floatPacketTapeFrom (fun k p => proposalFloatUniforms (uf k p) (vf k p))
          (fun k p => List.ofFn (ef k p)) source tail 0 (fuel + 1)) fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (rssaRealClock bounds) source sr) marks 0 m)) := by
  have href k (hk : k < m) us es extra := rssa_float_certificate_refines (rates k) (bounds k)
    (floatTimeSchedule (rssaFloatClock bounds ef) source start k)
    (ef k (source k)) (uf k (source k)) (vf k (source k))
    (fun j => -log ((source k).2.1 j)) (fun j => ((source k).2.2 j).1)
    (fun j => ((source k).2.2 j).2) d η (C.hc k hk) (C.hupper k hk) (C.hB k hk) (C.hg k hk).2.2.1
    (marks k) (by intro j; exact (mem_pi.mp (C.hg k hk).2.2.2) j (mem_univ _)) us es extra
  have hfin : ∀ k, k < m → ExecFloat.Binary.isFinite
      (floatTimeSchedule (rssaFloatClock bounds ef) source start (k + 1)) = true := by
    intro k hk
    have h := (C.hc k hk).clockValid
    rw [clockFlag, Bool.and_eq_true] at h
    exact h.1
  by_cases hstop : m ≤ fuel
  · apply float_packet_trajectory_close_absorb mf mr .rssa (by intro h; cases h) htransition states marks
      (rssaFloatClock bounds ef) (fun k p => proposalFloatUniforms (uf k p) (vf k p))
      (fun k p => List.ofFn (ef k p)) (rssaRealClock bounds) source tail start hf sr hr ε d δ fuel cap m
      hstop save
    · intro k hk us es
      have he := href k hk us es (cap - ((source k).1.1 + 1))
      rw [show (source k).1.1 + 1 + (cap - ((source k).1.1 + 1)) = cap by
        have := (C.hg k hk).1; omega] at he
      dsimp only [sampleEvent]
      rw [hm k, hb k]
      exact he.1
    · exact hfin
    · intro k hk
      have h := (C.hc k hk).clockValid
      rw [clockFlag, Bool.and_eq_true] at h
      exact float_le_of_lt_flag _ _ (C.hc k hk).nowFinite h.1 h.2
    · intro k hk
      unfold rssaRealClock rssaStoppingTime exponentialClock
      exact Finset.sum_nonneg (fun j _ => (div_pos
        (neg_pos.mpr (log_neg ((C.hg k hk).2.1 j).1 ((C.hg k hk).2.1 j).2)) (C.hB k hk)).le)
    · intro k hk
      simpa only [floatTimeSchedule, rssaFloatClock, rssaRealClock, rssaStoppingTime, exponentialClock,
        Finset.sum_div] using (href k hk [] [] 0).2
    · intro rng
      dsimp only [sampleEvent]
      rw [hm m, hb m]
      exact rssa_float_absorbing (rates m) (bounds m) _ rng cap (C.absorbBounds hstop)
        (floatTimeSchedule_finite _ _ _ m (start_finite_of_valid start hf C.hvalid) hfin)
        (C.absorbFinite hstop) (C.absorbInactive hstop)
    · exact fun k _ => hs k
    · exact C.hvalid
    · exact C.hstart
    · exact C.hhf
    · exact C.hh
    · exact C.h0
    · exact C.hd
    · exact C.hbudget
    · exact C.hmargin
  · have hm' : m = fuel + 1 := le_antisymm C.stop (by omega)
    subst hm'
    exact float_packet_trajectory_close_from mf mr .rssa (by intro h; cases h) htransition states marks
      (rssaFloatClock bounds ef) (fun k p => proposalFloatUniforms (uf k p) (vf k p))
      (fun k p => List.ofFn (ef k p)) (rssaRealClock bounds) source tail start hf sr hr ε d δ fuel cap save
      (rssa_float_local_refinement mf states marks rates bounds hm hb ef uf vf source start fuel cap d η
        (fun k hk => C.hupper k (by omega)) (fun k hk => C.hB k (by omega))
        (fun k hk => C.hg k (by omega)) (fun k hk => C.hc k (by omega)))
      hs C.hvalid C.hstart C.hhf C.hh C.h0 C.hd C.hbudget (fun k hk => C.hmargin k (by omega))

end JumpProcessesLean.Proofs
