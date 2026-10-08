import JumpProcessesLean.Proofs.StreamTape

/-!
# Direct method on IID streams

The public `simulate` driver with the Direct method, run on the random tape filled
from two independent IID Uniform(0,1) streams, has the marked-exponential stopped
trajectory law. No reaction-word decomposition is assumed: the word events are
derived from the streams and shown to be a partition of probability one.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- A Direct event reads one exponential-source uniform and one selection uniform. -/
noncomputable def directReader : StreamReader (ℝ × ℝ) where
  read ω := (ω (.inr 0), ω (.inl 0))
  usedU _ := 1
  usedV _ := 1
  good := univ
  measurable_read := by fun_prop
  measurable_usedU := measurable_const
  measurable_usedV := measurable_const
  measurableSet_good := MeasurableSet.univ
  ae_good := Filter.Eventually.of_forall (fun _ => trivial)
  determined := by
    intro ω _ ω' h
    refine ⟨trivial, ?_, rfl, rfl⟩
    have h1 := congrFun (congrArg Prod.fst h) 0
    have h2 := congrFun (congrArg Prod.snd h) 0
    simp only [streamsTake] at h1 h2
    simp only [Fin.val_zero] at h1 h2
    rw [h1, h2]

theorem directReader_law :
    iidStreams.map directReader.read = unitUniform.prod unitUniform := by
  have hcomp : directReader.read = (fun q : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (q.2 0, q.1 0)) ∘
      streamsTake 1 1 := rfl
  have he : (Measure.pi (fun _ : Fin 1 => unitUniform)).map (fun x => x 0) = unitUniform :=
    (measurePreserving_eval (fun _ : Fin 1 => unitUniform) 0).map_eq
  rw [hcomp, ← Measure.map_map (by fun_prop) (measurable_streamsTake 1 1), iidStreams_map_take]
  have hswap : (fun q : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (q.2 0, q.1 0)) =
      (Prod.map (fun x : Fin 1 → ℝ => x 0) (fun x : Fin 1 → ℝ => x 0)) ∘ Prod.swap := by
    funext q
    rfl
  rw [hswap, ← Measure.map_map (by fun_prop) measurable_swap, Measure.prod_swap,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), he]

lemma directParse_eq (K : ℕ) (ω : Streams) :
    readerParse (fun _ => directReader) K ω =
      (fun q : Fin K => (ω (.inr (K - 1 - q.val)), ω (.inl (K - 1 - q.val))), streamsDrop K K ω) := by
  induction K with
  | zero =>
    apply Prod.ext
    · funext q
      exact Fin.elim0 q
    · simp [readerParse]
  | succ K ih =>
    rw [readerParse_succ, Function.comp_apply, ih]
    apply Prod.ext
    · funext q
      cases q using Fin.cases with
      | zero =>
        simp [rawWordExtend, directReader, streamsDrop]
      | succ q =>
        have he : K + 1 - 1 - q.succ.val = K - 1 - q.val := by simp only [Fin.val_succ]; omega
        simp only [rawWordExtend, Fin.cases_succ, he]
    · simp only [StreamReader.rest, directReader, streamsDrop_drop]

lemma directParse_chronological (K : ℕ) (ω : Streams) (l : ℕ) (hl : l < K) :
    rawChronological (1 / 2, 1 / 2) (readerParse (fun _ => directReader) K ω).1 l =
      (ω (.inr l), ω (.inl l)) := by
  simp only [rawChronological, hl, dite_true, directParse_eq]
  have he : K - 1 - (K - 1 - l) = l := by omega
  rw [he]

lemma directPacketTape_eq {n : Nat} {σ : Type} (model : Model ℝ σ) (states : Nat → σ)
    (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (hr : ∀ k j, 0 ≤ rates k j) (hm : ∀ k, model.rates (states k) = Array.ofFn (rates k))
    (source : Nat → ℝ × ℝ) (tail : Tape ℝ) (k count : Nat) :
    let P := directPacketSpecification model states rates marks hr hm
    packetTapeFrom P.uniforms P.exponentials source tail k count =
      ⟨List.ofFn (fun i : Fin count => (source (k + i)).2) ++ tail.uniforms,
        List.ofFn (fun i : Fin count => -log (source (k + i)).1) ++ tail.exponentials⟩ := by
  dsimp only
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
    rw [packetTapeFrom, ih (k + 1)]
    simp only [directPacketSpecification, List.ofFn_succ, Fin.val_zero, add_zero, Fin.val_succ,
      List.cons_append, List.nil_append]
    simp only [Nat.add_assoc, Nat.add_comm 1]

/-! ### Direct reaction-word branches of the IID streams -/

section DirectWords

variable {σ : Type} {n : ℕ} (transition : σ → Fin (n + 1) → σ)
  (rates : σ → Fin (n + 1) → ℝ) (initial : σ)

/-- Direct primitive packets read from the streams, most recent first. -/
noncomputable def directParse (K : ℕ) (ω : Streams) : Fin K → ℝ × ℝ :=
  (readerParse (fun _ => directReader) K ω).1

lemma measurable_directParse (K : ℕ) : Measurable (directParse K) :=
  (measurable_readerParse _ K).fst

lemma directParse_law (K : ℕ) :
    iidStreams.map (directParse K) = rawWordLaw (fun _ => unitUniform.prod unitUniform) K := by
  have h := congrArg (fun μ => μ.map Prod.fst) (readerParse_law (fun _ => directReader) K)
  simp only [Measure.map_map measurable_fst (measurable_readerParse _ K)] at h
  rw [Measure.map_fst_prod, measure_univ, one_smul] at h
  have hp : directParse K = Prod.fst ∘ readerParse (fun _ => directReader) K := rfl
  rw [hp, h]
  simp only [directReader_law]

/-- The selection uniform of step `l` chooses the `l`th reaction of `w`. -/
noncomputable def directBranchSet {K : ℕ} (w : Fin K → Fin (n + 1)) (l : ℕ) : Set (ℝ × ℝ) :=
  {x | selection (List.ofFn (completedRates (rates (stateAlongWord transition initial (extendMarks w) l))))
    x.2 = some (extendMarks w l).val}

lemma measurableSet_directBranchSet {K : ℕ} (w : Fin K → Fin (n + 1)) (l : ℕ) :
    MeasurableSet (directBranchSet transition rates initial w l) :=
  ((measurable_chooseAux _ _ _).comp (measurable_snd.mul_const _)) (measurableSet_singleton _)

/-- The streams realize reaction word `w` under the Direct method. -/
noncomputable def directWordEvent {K : ℕ} (w : Fin K → Fin (n + 1)) : Set Streams :=
  directParse K ⁻¹' (Set.univ.pi (fun q : Fin K => directBranchSet transition rates initial w (K - 1 - q)))

lemma measurableSet_directWordEvent {K : ℕ} (w : Fin K → Fin (n + 1)) :
    MeasurableSet (directWordEvent transition rates initial w) :=
  measurable_directParse K (MeasurableSet.univ_pi (fun q => measurableSet_directBranchSet _ _ _ w _))

lemma directWordEvent_branch {K : ℕ} (w : Fin K → Fin (n + 1)) :
    (iidStreams.restrict (directWordEvent transition rates initial w)).map (directParse K) =
      rawWordLaw (fun l => directPacketInputs (rates (stateAlongWord transition initial (extendMarks w) l))
        (extendMarks w l)) K := by
  unfold directWordEvent
  rw [← Measure.restrict_map (measurable_directParse K)
    (MeasurableSet.univ_pi (fun q => measurableSet_directBranchSet _ _ _ w _)), directParse_law,
    ← rawWordLaw_restrict _ (fun _ => inferInstance) _ (measurableSet_directBranchSet _ _ _ w)]
  rfl

/-- Direct real clock of a primitive packet at the state of step `l`. -/
noncomputable def directWordClock {K : ℕ} (w : Fin K → Fin (n + 1)) (l : ℕ) (p : ℝ × ℝ) : ℝ :=
  exponentialClock (∑ j, completedRates (rates (stateAlongWord transition initial (extendMarks w) l)) j) p.1

lemma measurable_directWordClock {K : ℕ} (w : Fin K → Fin (n + 1)) (l : ℕ) :
    Measurable (directWordClock transition rates initial w l) :=
  (measurable_exponentialClock _).comp measurable_fst

lemma directWord_holding_law (hr : ∀ x j, 0 ≤ rates x j) {K : ℕ} (w : Fin K → Fin (n + 1)) :
    (rawWordLaw (fun l => directPacketInputs (rates (stateAlongWord transition initial (extendMarks w) l))
        (extendMarks w l)) K).map (rawWordHoldings (directWordClock transition rates initial w) K) =
      targetWordLaw (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks w) l)))
        (extendMarks w) K := by
  rw [raw_word_holding_law _ (fun l => by unfold directPacketInputs; infer_instance) _
    (measurable_directWordClock _ _ _ w)]
  have h (k : Nat) : independentWordLaw (fun l =>
      (directPacketInputs (rates (stateAlongWord transition initial (extendMarks w) l))
        (extendMarks w l)).map (directWordClock transition rates initial w l)) k =
      targetWordLaw (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks w) l)))
        (extendMarks w) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hc : (directPacketInputs (rates (stateAlongWord transition initial (extendMarks w) k))
          (extendMarks w k)).map (directWordClock transition rates initial w k) =
          ENNReal.ofReal (completedRates (rates (stateAlongWord transition initial (extendMarks w) k))
            (extendMarks w k) / (∑ j, completedRates
              (rates (stateAlongWord transition initial (extendMarks w) k)) j)) •
            expMeasure (∑ j, completedRates (rates (stateAlongWord transition initial (extendMarks w) k)) j) :=
        direct_packet_clock_law _ (fun j => hr _ j) _
      rw [independentWordLaw, targetWordLaw, ih, hc]
  exact h K

lemma directWordEvent_mass (hr : ∀ x j, 0 ≤ rates x j) {K : ℕ} (w : Fin K → Fin (n + 1)) :
    iidStreams (directWordEvent transition rates initial w) = pathWordWeight transition rates initial w := by
  have h1 : iidStreams (directWordEvent transition rates initial w) =
      ((iidStreams.restrict (directWordEvent transition rates initial w)).map (directParse K)) univ := by
    rw [Measure.map_apply (measurable_directParse K) MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
  rw [h1, directWordEvent_branch, ← preimage_univ (f := rawWordHoldings _ K),
    ← Measure.map_apply (measurable_rawWordHoldings _ (measurable_directWordClock _ _ _ w) K)
      MeasurableSet.univ, directWord_holding_law _ _ _ hr,
    target_word_mass _ (fun l => completedRates_positive_total _)]
  unfold pathWordWeight
  apply Finset.prod_congr rfl
  intro q _
  simp only [extendMarks, q.isLt, dite_true]

lemma directWordEvent_total (hr : ∀ x j, 0 ≤ rates x j) (K : ℕ) :
    ∑ w : Fin K → Fin (n + 1), iidStreams (directWordEvent transition rates initial w) = 1 := by
  simp_rw [directWordEvent_mass _ _ _ hr]
  exact path_word_weights_normalize transition rates hr K initial

lemma directWordEvent_disjoint (K : ℕ) :
    Pairwise (Function.onFun Disjoint
      (fun w : Fin K → Fin (n + 1) => directWordEvent transition rates initial w)) := by
  intro w w' hww
  rw [Function.onFun, Set.disjoint_left]
  intro ω hω hω'
  apply hww
  apply words_eq_of_sequential_choice
  intro l hl hprev
  have hq : K - 1 - (⟨K - 1 - l, by omega⟩ : Fin K).val = l := by simp only; omega
  have h1 := (Set.mem_univ_pi.mp hω) ⟨K - 1 - l, by omega⟩
  have h2 := (Set.mem_univ_pi.mp hω') ⟨K - 1 - l, by omega⟩
  simp only [hq, directBranchSet, mem_ofPred_eq] at h1 h2
  have hstates : stateAlongWord transition initial (extendMarks w) l =
      stateAlongWord transition initial (extendMarks w') l :=
    stateAlongWord_congr transition initial _ _ l (extendMarks_agree w w' l (fun j hj hjK =>
      hprev j hj))
  have hmw : (extendMarks w l) = w ⟨l, hl⟩ := by simp [extendMarks, hl]
  have hmw' : (extendMarks w' l) = w' ⟨l, hl⟩ := by simp [extendMarks, hl]
  rw [hstates] at h1
  rw [h1, hmw, hmw'] at h2
  exact Fin.ext (Option.some_injective _ h2)

end DirectWords

/-- On every realized Direct word, the public driver executes the stream transcript. -/
theorem direct_stream_driver_executes {σ : Type} {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper)
    (initial : σ) (start horizon : ℝ) (hstart : start < horizon)
    (fuel cap : Nat) (saveEvents : Bool) (c d : Nat)
    (w : Fin (fuel + 1) → Fin (n + 1)) (ω : Streams) (hω : ∀ x, ω x ∈ Ioo (0 : ℝ) 1)
    (hE : ω ∈ directWordEvent transition rates initial w) :
    observeRun (simulate realArithmetic (tapeSource ℝ) model .direct initial start horizon
      (streamTape (fuel + 1 + c) (fuel + 1 + d) ω) fuel saveEvents cap) =
    holdingSimulationObservation model (stateAlongWord transition initial (extendMarks w))
      (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w) start horizon
      fuel saveEvents (rawWordHoldings (directWordClock transition rates initial w) (fuel + 1)
        (directParse (fuel + 1) ω)) := by
  let states := stateAlongWord transition initial (extendMarks w)
  let rr := fun l => rates (states l)
  let P := directPacketSpecification model states rr (extendMarks w)
    (fun l j => C.nonnegative _ j) (fun l => C.rates_eq _)
  have hgood : RawWordGood P.good (fuel + 1) (directParse (fuel + 1) ω) := by
    apply rawWordGood_of_index
    intro q
    have hb := (Set.mem_univ_pi.mp hE) q
    have hpq : directParse (fuel + 1) ω q =
        (ω (.inr (fuel + 1 - 1 - q.val)), ω (.inl (fuel + 1 - 1 - q.val))) := by
      simp only [directParse, directParse_eq]
    rw [hpq] at hb ⊢
    exact ⟨hω _, hω _, hb⟩
  have htape : streamTape (fuel + 1 + c) (fuel + 1 + d) ω =
      packetTapeFrom P.uniforms P.exponentials (rawChronological (1 / 2, 1 / 2) (directParse (fuel + 1) ω))
        (streamTape c d (streamsDrop (fuel + 1) (fuel + 1) ω)) 0 (fuel + 1) := by
    rw [directPacketTape_eq, streamTape_split]
    have hsrc : ∀ i : Fin (fuel + 1), rawChronological (1 / 2, 1 / 2) (directParse (fuel + 1) ω) (0 + i.val) =
        (ω (.inr i), ω (.inl i)) := by
      intro i
      rw [zero_add]
      exact directParse_chronological (fuel + 1) ω i i.isLt
    simp only [hsrc]
  have hinit : initial = states 0 := rfl
  rw [htape, hinit, packet_driver_executes_from model .direct states rr (extendMarks w) P
    (1 / 2, 1 / 2) (fun l => C.transition_eq _ _) start horizon hstart fuel cap saveEvents
    (directParse (fuel + 1) ω) hgood (fun _ _ => Nat.zero_le _)]
  rfl

/-- The actual Direct simulation on IID streams has the target stopped-trajectory
law. The tape contains at least as many uniforms and exponentials as the event
budget can consume. -/
theorem direct_iid_simulation_law {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper)
    (initial : σ) (start horizon : ℝ) (hstart : start < horizon)
    (fuel cap : Nat) (saveEvents : Bool) (a b : Nat) (ha : fuel + 1 ≤ a) (hb : fuel + 1 ≤ b)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts => observable (holdingSimulationObservation model states
        (fun l => rates (states l)) marks start horizon fuel saveEvents ts))) :
    iidStreams.map (fun ω => observable (observeRun (simulate realArithmetic (tapeSource ℝ)
      model .direct initial start horizon (streamTape a b ω) fuel saveEvents cap))) =
    targetSimulationLaw model transition rates initial start horizon fuel saveEvents observable := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
  let E := fun w : Fin (fuel + 1) → Fin (n + 1) => directWordEvent transition rates initial w
  let G := fun (w : Fin (fuel + 1) → Fin (n + 1)) (ω : Streams) =>
    observable (holdingSimulationObservation model (stateAlongWord transition initial (extendMarks w))
      (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w) start horizon
      fuel saveEvents (rawWordHoldings (directWordClock transition rates initial w) (fuel + 1)
        (directParse (fuel + 1) ω)))
  have hmh : ∀ w : Fin (fuel + 1) → Fin (n + 1),
      Measurable (rawWordHoldings (directWordClock transition rates initial w) (fuel + 1)) := fun w =>
    measurable_rawWordHoldings _ (measurable_directWordClock _ _ _ w) _
  have hG : ∀ w, Measurable (G w) := fun w =>
    (hobs w).comp ((hmh w).comp (measurable_directParse _))
  have hFG : ∀ w, ∀ᵐ ω ∂iidStreams, ω ∈ E w →
      observable (observeRun (simulate realArithmetic (tapeSource ℝ) model .direct initial start
        horizon (streamTape (fuel + 1 + c) (fuel + 1 + d) ω) fuel saveEvents cap)) = G w ω := by
    intro w
    filter_upwards [iidStreams_ae_mem_Ioo] with ω hω hE
    exact congrArg observable (direct_stream_driver_executes model transition rates lower upper C initial
      start horizon hstart fuel cap saveEvents c d w ω hω hE)
  rw [iid_word_decomposition E (fun w => measurableSet_directWordEvent _ _ _ w)
    (directWordEvent_disjoint _ _ _ (fuel + 1)) (directWordEvent_total _ _ _ C.nonnegative (fuel + 1))
    _ G hG hFG]
  unfold targetSimulationLaw
  congr 1
  funext w
  have h1 := Measure.map_map (μ := iidStreams.restrict (E w)) (hobs w)
    ((hmh w).comp (measurable_directParse (fuel + 1)))
  have h2 := Measure.map_map (μ := iidStreams.restrict (E w)) (hmh w) (measurable_directParse (fuel + 1))
  rw [← h2, directWordEvent_branch, directWord_holding_law _ _ _ C.nonnegative] at h1
  exact h1.symm

end JumpProcessesLean.Proofs
