import JumpProcessesLean.Proofs.PacketSimulation

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def directPacketInputs {n : Nat} (rates : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Measure (ℝ × ℝ) :=
  (unitUniform.prod unitUniform).restrict
    {p | selection (List.ofFn (completedRates rates)) p.2 = some i.val}

noncomputable def DirectPacketGood {n : Nat} (rates : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (p : ℝ × ℝ) : Prop :=
  p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo 0 1 ∧
    selection (List.ofFn (completedRates rates)) p.2 = some i.val

lemma measurable_DirectPacketGood {n : Nat} (rates : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    MeasurableSet {p | DirectPacketGood rates i p} := by
  have hm : Measurable (fun p : ℝ × ℝ => selection (List.ofFn (completedRates rates)) p.2) :=
    (measurable_chooseAux _ _ _).comp (measurable_snd.mul_const _)
  convert
    ((measurable_fst (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))).inter
      (measurable_snd (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)))).inter
      (hm (measurableSet_singleton (some i.val))) using 1
  ext p
  simp only [DirectPacketGood, mem_setOf_eq, mem_preimage, mem_inter_iff, mem_singleton_iff, and_assoc]

theorem direct_packet_good_ae {n : Nat} (rates : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ∀ᵐ p ∂directPacketInputs rates i, DirectPacketGood rates i p := by
  unfold directPacketInputs
  have hm : Measurable (fun p : ℝ × ℝ => selection (List.ofFn (completedRates rates)) p.2) :=
    (measurable_chooseAux _ _ _).comp (measurable_snd.mul_const _)
  filter_upwards [ae_restrict_of_ae unitUniform_pair_ae_mem,
    ae_restrict_mem (hm (measurableSet_singleton (some i.val)))] with p hp hs
  exact ⟨hp.1, hp.2, hs⟩

theorem direct_packet_clock_law {n : Nat} (rates : Fin (n + 1) → ℝ)
    (hr : ∀ j, 0 ≤ rates j) (i : Fin (n + 1)) :
    (directPacketInputs rates i).map (fun p => exponentialClock (∑ j, completedRates rates j) p.1) =
      ENNReal.ofReal (completedRates rates i / (∑ j, completedRates rates j)) •
        expMeasure (∑ j, completedRates rates j) := by
  have hn : ∀ a ∈ List.ofFn (completedRates rates), 0 ≤ a := by
    intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha; exact completedRates_nonnegative rates hr j
  have hA : 0 < (List.ofFn (completedRates rates)).sum := by
    simpa only [List.sum_ofFn] using completedRates_positive_total rates
  have hclock : Measurable (fun p : ℝ × ℝ => exponentialClock (∑ j, completedRates rates j) p.1) :=
    (measurable_exponentialClock _).comp measurable_fst
  ext s hs
  rw [directPacketInputs, Measure.map_apply hclock hs, Measure.restrict_apply (hclock hs)]
  have he : (fun p : ℝ × ℝ => exponentialClock (∑ j, completedRates rates j) p.1) ⁻¹' s ∩
      {p | selection (List.ofFn (completedRates rates)) p.2 = some i.val} =
      {p | exponentialClock (List.ofFn (completedRates rates)).sum p.1 ∈ s ∧
        selection (List.ofFn (completedRates rates)) p.2 = some i.val} := by
    ext p; simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, List.sum_ofFn]
  rw [he, direct_pair_probability _ hn hA i.val (by simpa using i.isLt) s hs,
    Measure.smul_apply, smul_eq_mul]
  simp only [List.getElem_ofFn, List.sum_ofFn]
  change expMeasure (∑ j, completedRates rates j) s *
    ENNReal.ofReal (completedRates rates i / (∑ j, completedRates rates j)) = _
  exact mul_comm _ _

lemma direct_real_absorbing {n : Nat} (rates : Fin (n + 1) → ℝ)
    (hr : ∀ j, 0 ≤ rates j) (hA : ¬0 < ∑ j, rates j) (now : ℝ) (rng : Tape ℝ) :
    direct realArithmetic (tapeSource ℝ) (Array.ofFn rates) now rng = .ok (none, rng) := by
  have hn : ∀ a ∈ (Array.ofFn rates).toList, 0 ≤ a := by
    intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (by simpa only [Array.toList_ofFn] using ha); exact hr j
  unfold direct
  rw [checkRates_real _ hn]
  simp only [Bind.bind, Except.bind, sumRates_real, Array.toList_ofFn, List.sum_ofFn]
  simp only [realArithmetic,
    Bool.not_true, Bool.false_eq_true, ite_false, hA, decide_false, Bool.not_false, ite_true,
    Pure.pure, Except.pure]

noncomputable def directPacketSpecification {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (hr : ∀ k j, 0 ≤ rates k j) (hm : ∀ k, model.rates (states k) = Array.ofFn (rates k)) :
    PacketSpecification (γ := ℝ × ℝ) model .direct states rates marks where
  clock := fun k p => exponentialClock (∑ j, completedRates (rates k) j) p.1
  uniforms := fun _ p => [p.2]
  exponentials := fun _ p => [-log p.1]
  cost := fun _ _ => 0
  good := fun k => DirectPacketGood (rates k) (marks k)
  uncached := by intro h; cases h
  execute := by
    intro k p hp hA cap hc now us es
    dsimp only [sampleEvent]
    rw [hm k]
    have hn : ∀ a ∈ (Array.ofFn (rates k)).toList, 0 ≤ a := by
      intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (by simpa only [Array.toList_ofFn] using ha); exact hr k j
    have hs : selection (Array.ofFn (rates k)).toList p.2 = some (marks k).val := by
      simpa only [completedRates, hA, ite_true, Array.toList_ofFn] using hp.2.2
    have hex := direct_real_suffix_executes (Array.ofFn (rates k)) hn
      (by simpa only [Array.toList_ofFn, List.sum_ofFn] using hA) now
      (-log p.1) p.2 (neg_pos.mpr (log_neg hp.1.1 hp.1.2)) ⟨hp.2.1.1.le, hp.2.1.2⟩
      (marks k).val hs us es
    simpa only [List.singleton_append, Array.toList_ofFn, List.sum_ofFn, completedRates, hA,
      ite_true, exponentialClock] using hex
  absorb := by
    intro k hA cap now rng
    dsimp only [sampleEvent]
    rw [hm k]
    exact direct_real_absorbing _ (hr k) hA now rng

/-- The native Direct simulation's complete random-tape pushforward on a word
equals the same stopped target used by the persistent NRM simulator. -/
theorem direct_simulation_word_law {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (hr : ∀ l j, 0 ≤ rates l j)
    (hm : ∀ l, model.rates (states l) = Array.ofFn (rates l))
    (hs : ∀ l, model.transition (states l) (marks l).val = .ok (states (l + 1)))
    (start horizon : ℝ) (hstart : start < horizon) (fuel : Nat) (saveEvents : Bool)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : Measurable (fun ts => observable
      (holdingSimulationObservation model states rates marks start horizon fuel saveEvents ts))) :
    let P := directPacketSpecification model states rates marks hr hm
    (rawWordLaw (fun k => directPacketInputs (rates k) (marks k)) (fuel + 1)).map
      (fun p => observable (packetCompiledRun P (1 / 2, 1 / 2) start horizon fuel saveEvents p)) =
    (targetWordLaw (fun l => completedRates (rates l)) marks (fuel + 1)).map
      (fun ts => observable (holdingSimulationObservation model states rates marks start horizon fuel saveEvents ts)) := by
  dsimp only
  apply packet_simulation_word_law model .direct states rates marks
    (directPacketSpecification model states rates marks hr hm)
    (fun k => directPacketInputs (rates k) (marks k))
    (fun k => by unfold directPacketInputs; infer_instance)
    (fun k => measurable_DirectPacketGood _ _)
    (fun k => direct_packet_good_ae _ _)
    (fun k => (measurable_exponentialClock _).comp measurable_fst)
    (fun k => direct_packet_clock_law _ (hr k) _) (1 / 2, 1 / 2) hs start horizon hstart fuel saveEvents observable hobs

end JumpProcessesLean.Proofs
