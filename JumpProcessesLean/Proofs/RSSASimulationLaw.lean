import JumpProcessesLean.Proofs.PacketSimulation
import JumpProcessesLean.Proofs.RSSATapeSuffix
import JumpProcessesLean.Proofs.RSSAStoppingProbability

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def RSSAUniformGood {n : Nat} (rates lower upper : List ℝ)
    (p : RSSAStoppingInput n) : Prop :=
  (∀ j, p.2.1 j ∈ Ioo 0 1) ∧
  (∀ j, (p.2.2 j).1 ∈ Ioo 0 1 ∧ (p.2.2 j).2 ∈ Ioo 0 1) ∧
  p.2.2 ∈ proposalBranch rates lower upper p.1.1 p.1.2.val

lemma measurable_RSSAUniformGood {n : Nat} (rates lower upper : List ℝ) :
    MeasurableSet {p : RSSAStoppingInput n | RSSAUniformGood rates lower upper p} := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro b
  change MeasurableSet {p : RSSABranchInput b.1 |
    (∀ j, p.1 j ∈ Ioo 0 1) ∧
    (∀ j, (p.2 j).1 ∈ Ioo 0 1 ∧ (p.2 j).2 ∈ Ioo 0 1) ∧
    p.2 ∈ proposalBranch rates lower upper b.1 b.2.val}
  have h1 : MeasurableSet {p : RSSABranchInput b.1 | ∀ j, p.1 j ∈ Ioo 0 1} := by measurability
  have h2 : MeasurableSet {p : RSSABranchInput b.1 |
      ∀ j, (p.2 j).1 ∈ Ioo 0 1 ∧ (p.2 j).2 ∈ Ioo 0 1} := by measurability
  exact h1.inter (h2.inter (measurable_snd (measurable_proposalBranch _ _ _ _ _)))

lemma rssa_uniform_good_ae {n : Nat} (rates lower upper : List ℝ) :
    ∀ᵐ p ∂rssaStoppingInputs (n := n) rates lower upper,
      RSSAUniformGood rates lower upper p := by
  rw [rssaStoppingInputs, Measure.ae_sum_iff]
  intro b
  rw [ae_map_iff (measurable_branch_injection b).aemeasurable (measurable_RSSAUniformGood _ _ _)]
  have hp : ∀ᵐ p : RSSABranchInput b.1
      ∂(Measure.pi (fun _ => unitUniform)).prod (Measure.pi (fun _ => unitUniform.prod unitUniform)),
      (∀ j, p.1 j ∈ Ioo 0 1) ∧ (∀ j, (p.2 j).1 ∈ Ioo 0 1 ∧ (p.2 j).2 ∈ Ioo 0 1) := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [unitUniform_vector_ae_mem (b.1 + 1)] with u hu
    have hv : ∀ᵐ v : Fin (b.1 + 1) → ℝ × ℝ ∂Measure.pi (fun _ => unitUniform.prod unitUniform),
        ∀ j, (v j).1 ∈ Ioo 0 1 ∧ (v j).2 ∈ Ioo 0 1 := by
      rw [ae_all_iff]
      intro j
      exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (b.1 + 1) => unitUniform.prod unitUniform)
        (i := j)).eventually unitUniform_pair_ae_mem
    exact hv.mono (fun v hv => ⟨hu, hv⟩)
  filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem
    (MeasurableSet.prod MeasurableSet.univ (measurable_proposalBranch rates lower upper b.1 b.2.val))]
    with p hp hb
  exact ⟨hp.1, hp.2, hb.2⟩

noncomputable def rssaPacketInputs {n : Nat} (rates lower upper : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : Measure (RSSAStoppingInput (n + 1)) :=
  (rssaStoppingInputs (List.ofFn (completedRates rates))
    (List.ofFn (completedLower rates lower)) (List.ofFn (completedUpper rates upper))).restrict
      {p | rssaStoppingMark p = i}

noncomputable def RSSAPacketGood {n : Nat} (rates lower upper : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (p : RSSAStoppingInput (n + 1)) : Prop :=
  RSSAUniformGood (List.ofFn (completedRates rates)) (List.ofFn (completedLower rates lower))
    (List.ofFn (completedUpper rates upper)) p ∧ rssaStoppingMark p = i

lemma measurable_RSSAPacketGood {n : Nat} (rates lower upper : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : MeasurableSet {p | RSSAPacketGood rates lower upper i p} :=
  (measurable_RSSAUniformGood _ _ _).inter
    ((measurable_rssaStoppingMark _) (measurableSet_singleton i))

lemma rssa_packet_good_ae {n : Nat} (rates lower upper : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ∀ᵐ p ∂rssaPacketInputs rates lower upper i, RSSAPacketGood rates lower upper i p := by
  unfold rssaPacketInputs
  filter_upwards [ae_restrict_of_ae (rssa_uniform_good_ae _ _ _),
    ae_restrict_mem ((measurable_rssaStoppingMark _) (measurableSet_singleton i))] with p hp hi
  exact ⟨hp, hi⟩

lemma completed_rssa_data {n : Nat} (rates lower upper : Fin (n + 1) → ℝ)
    (hb : ∀ j, 0 ≤ lower j ∧ lower j ≤ rates j ∧ rates j ≤ upper j) :
    ((List.ofFn (completedLower rates lower)).length = (List.ofFn (completedRates rates)).length ∧ (List.ofFn (completedUpper rates upper)).length = (List.ofFn (completedRates rates)).length) ∧
    (∀ (j : Nat) (hj : j < (List.ofFn (completedRates rates)).length), 0 ≤ (List.ofFn (completedLower rates lower))[j]'(by simpa only [List.length_ofFn] using hj) ∧
      (List.ofFn (completedLower rates lower))[j]'(by simpa only [List.length_ofFn] using hj) ≤ (List.ofFn (completedRates rates))[j] ∧ (List.ofFn (completedRates rates))[j] ≤ (List.ofFn (completedUpper rates upper))[j]'(by simpa only [List.length_ofFn] using hj)) ∧
    0 < (List.ofFn (completedRates rates)).sum ∧ 0 < (List.ofFn (completedUpper rates upper)).sum ∧ (List.ofFn (completedRates rates)).sum ≤ (List.ofFn (completedUpper rates upper)).sum := by
  have hc := completedBounds_valid rates lower upper hb
  have hAB : (∑ j, completedRates rates j) ≤ ∑ j, completedUpper rates upper j :=
    Finset.sum_le_sum (fun j _ => (hc j).2.2)
  refine ⟨by simp only [List.length_ofFn, and_self], ?_, ?_, ?_, ?_⟩
  · intro j hj
    simpa only [List.getElem_ofFn] using hc ⟨j, by simpa only [List.length_ofFn] using hj⟩
  · simpa only [List.sum_ofFn] using completedRates_positive_total rates
  · simpa only [List.sum_ofFn] using (completedRates_positive_total rates).trans_le hAB
  · simpa only [List.sum_ofFn] using hAB

lemma rssa_packet_finite {n : Nat} (rates lower upper : Fin (n + 1) → ℝ)
    (hb : ∀ j, 0 ≤ lower j ∧ lower j ≤ rates j ∧ rates j ≤ upper j) (i : Fin (n + 1)) :
    IsFiniteMeasure (rssaPacketInputs rates lower upper i) := by
  have h := completed_rssa_data rates lower upper hb
  letI := rssa_stopping_inputs_probability (n := n + 1) (List.ofFn (completedRates rates))
    (List.ofFn (completedLower rates lower)) (List.ofFn (completedUpper rates upper))
    (by simp only [List.length_ofFn]) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  unfold rssaPacketInputs
  infer_instance

lemma rssa_packet_clock_law {n : Nat} (rates lower upper : Fin (n + 1) → ℝ)
    (hb : ∀ j, 0 ≤ lower j ∧ lower j ≤ rates j ∧ rates j ≤ upper j) (i : Fin (n + 1)) :
    (rssaPacketInputs rates lower upper i).map
      (rssaStoppingTime (List.ofFn (completedUpper rates upper))) =
      ENNReal.ofReal (completedRates rates i / (∑ j, completedRates rates j)) •
        expMeasure (∑ j, completedRates rates j) := by
  have h := completed_rssa_data rates lower upper hb
  ext s hs
  rw [rssaPacketInputs, Measure.map_apply (measurable_rssaStoppingTime _) hs,
    Measure.restrict_apply ((measurable_rssaStoppingTime _) hs)]
  change (rssaStoppingInputs _ _ _) {p | rssaStoppingTime _ p ∈ s ∧ rssaStoppingMark p = i} = _
  rw [rssa_stopping_input_marked_law _ _ _ (by simp only [List.length_ofFn])
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 i s hs, Measure.smul_apply, smul_eq_mul]
  simp only [List.getElem_ofFn, List.sum_ofFn]

lemma rssa_real_absorbing {n : Nat} (rates lower upper : Fin (n + 1) → ℝ)
    (hb : ∀ j, 0 ≤ lower j ∧ lower j ≤ rates j ∧ rates j ≤ upper j)
    (hA : ¬0 < ∑ j, rates j) (now : ℝ) (rng : Tape ℝ) (cap : Nat) :
    rssa realArithmetic (tapeSource ℝ) (Array.ofFn rates) ⟨Array.ofFn lower, Array.ofFn upper⟩
      now rng cap = .ok (none, rng) := by
  have hz (j : Fin (n + 1)) : rates j = 0 := by
    have hh : rates j ≤ ∑ j, rates j := Finset.single_le_sum
      (fun j _ => (hb j).1.trans (hb j).2.1) (Finset.mem_univ j)
    have hn := (hb j).1.trans (hb j).2.1
    linarith
  have hany : (Array.ofFn rates).any (realArithmetic.lt realArithmetic.zero) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hh
    obtain ⟨j, hj, hp⟩ := Array.any_eq_true.mp hh
    simp only [Array.getElem_ofFn, realArithmetic, hz, lt_self_iff_false, decide_false,
      Bool.false_eq_true] at hp
  simp only [realArithmetic] at hany
  unfold rssa
  rw [checkBounds_real _ _ (by simp only [Array.size_ofFn, and_self])
    (by intro j hj; simpa only [Array.getElem_ofFn] using hb ⟨j, by simpa only [Array.size_ofFn] using hj⟩)]
  simp only [Bind.bind, Except.bind]
  simp only [realArithmetic, hany, Bool.not_true,
    Bool.false_eq_true, ite_false, Bool.not_false, ite_true, Pure.pure, Except.pure]

noncomputable def rssaPacketSpecification {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates lower upper : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (hb : ∀ k j, 0 ≤ lower k j ∧ lower k j ≤ rates k j ∧ rates k j ≤ upper k j)
    (hm : ∀ k, model.rates (states k) = Array.ofFn (rates k))
    (hbounds : ∀ k, model.bounds (states k) = ⟨Array.ofFn (lower k), Array.ofFn (upper k)⟩) :
    PacketSpecification (γ := RSSAStoppingInput (n + 1)) model .rssa states rates marks where
  clock := fun k => rssaStoppingTime (List.ofFn (completedUpper (rates k) (upper k)))
  uniforms := fun _ p => proposalUniforms (List.ofFn (fun j => (p.2.1 j, p.2.2 j)))
  exponentials := fun _ p => proposalExponentials (List.ofFn (fun j => (p.2.1 j, p.2.2 j)))
  cost := fun _ p => p.1.1 + 1
  good := fun k => RSSAPacketGood (rates k) (lower k) (upper k) (marks k)
  uncached := by intro h; cases h
  execute := by
    intro k p hp hA cap hcap now us es
    dsimp only [sampleEvent]
    rw [hm k, hbounds k]
    have hAB : (∑ j, rates k j) ≤ ∑ j, upper k j := Finset.sum_le_sum (fun j _ => (hb k j).2.2)
    have hB : 0 < (Array.ofFn (upper k)).toList.sum := by
      simpa only [Array.toList_ofFn, List.sum_ofFn] using hA.trans_le hAB
    have hu : ∀ a ∈ (Array.ofFn (upper k)).toList, 0 ≤ a := by
      intro a ha
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (by simpa only [Array.toList_ofFn] using ha)
      exact ((hb k j).1.trans (hb k j).2.1).trans (hb k j).2.2
    have hbranch : p.2.2 ∈ proposalBranch (Array.ofFn (rates k)).toList
        (Array.ofFn (lower k)).toList (Array.ofFn (upper k)).toList p.1.1 p.1.2.val := by
      simpa only [RSSAUniformGood, completedRates, completedLower, completedUpper,
        hA, ite_true, Array.toList_ofFn] using hp.1.2.2
    rw [rssa_real_calls_proposals _ _ (by simp only [Array.size_ofFn, and_self])
      (by intro j hj; simpa only [Array.getElem_ofFn] using hb k ⟨j, by simpa only [Array.size_ofFn] using hj⟩)
      (by simpa only [Array.toList_ofFn, List.sum_ofFn] using hA) hB]
    have he := rssa_uniform_branch_suffix_executes (Array.ofFn (rates k))
      ⟨Array.ofFn (lower k), Array.ofFn (upper k)⟩ hu hB p.1.1 p.1.2.val p.2.1 p.2.2
      hp.1.1 hp.1.2.1 hbranch now us es (cap - (p.1.1 + 1))
    rw [show p.1.1 + 1 + (cap - (p.1.1 + 1)) = cap by omega] at he
    have hi : p.1.2 = marks k := hp.2
    simpa only [Array.toList_ofFn, rssaStoppingTime, completedUpper, hA, ite_true, hi] using he
  absorb := by
    intro k hA cap now rng
    dsimp only [sampleEvent]
    rw [hm k, hbounds k]
    exact rssa_real_absorbing _ _ _ (hb k) hA now rng cap

/-- Full native RSSA driver law from independent primitive first-success packets.
The adaptive transcript cap realizes the unbounded algorithm; fixed cap failure
probabilities are handled separately by `rssa_validated_cap_probability`. -/
theorem rssa_simulation_word_law {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (states : Nat → σ) (rates lower upper : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1))
    (hb : ∀ k j, 0 ≤ lower k j ∧ lower k j ≤ rates k j ∧ rates k j ≤ upper k j)
    (hm : ∀ k, model.rates (states k) = Array.ofFn (rates k))
    (hbounds : ∀ k, model.bounds (states k) = ⟨Array.ofFn (lower k), Array.ofFn (upper k)⟩)
    (hs : ∀ k, model.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start horizon : ℝ) (hstart : start < horizon) (fuel : Nat) (saveEvents : Bool)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : Measurable (fun ts => observable
      (holdingSimulationObservation model states rates marks start horizon fuel saveEvents ts))) :
    let P := rssaPacketSpecification model states rates lower upper marks hb hm hbounds
    (rawWordLaw (fun k => rssaPacketInputs (rates k) (lower k) (upper k) (marks k)) (fuel + 1)).map
      (fun p => observable (packetCompiledRun P ⟨(0, 0), (fun _ => 1 / 2, fun _ => (1 / 2, 1 / 2))⟩
        start horizon fuel saveEvents p)) =
    (targetWordLaw (fun l => completedRates (rates l)) marks (fuel + 1)).map
      (fun ts => observable (holdingSimulationObservation model states rates marks start horizon fuel saveEvents ts)) := by
  dsimp only
  apply packet_simulation_word_law model .rssa states rates marks
    (rssaPacketSpecification model states rates lower upper marks hb hm hbounds)
    (fun k => rssaPacketInputs (rates k) (lower k) (upper k) (marks k))
    (fun k => rssa_packet_finite _ _ _ (hb k) _)
    (fun k => measurable_RSSAPacketGood _ _ _ _)
    (fun k => rssa_packet_good_ae _ _ _ _)
    (fun k => measurable_rssaStoppingTime _)
    (fun k => rssa_packet_clock_law _ _ _ (hb k) _) _ hs start horizon hstart fuel saveEvents observable hobs

end JumpProcessesLean.Proofs
