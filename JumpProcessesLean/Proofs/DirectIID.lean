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
  set K := fuel + 1 with hK
  let parse : Streams → Fin K → ℝ × ℝ := fun ω => (readerParse (fun _ => directReader) K ω).1
  have hparse : Measurable parse := (measurable_readerParse _ K).fst
  have hparse_law : iidStreams.map parse = rawWordLaw (fun _ => unitUniform.prod unitUniform) K := by
    have h := congrArg (fun μ => μ.map Prod.fst) (readerParse_law (fun _ => directReader) K)
    simp only [Measure.map_map measurable_fst (measurable_readerParse _ K)] at h
    rw [Measure.map_fst_prod, measure_univ, one_smul] at h
    have hp : parse = Prod.fst ∘ readerParse (fun _ => directReader) K := rfl
    rw [hp, h]
    simp only [directReader_law]
  -- Word-specific data.
  let states : (Fin K → Fin (n + 1)) → Nat → σ := fun w =>
    stateAlongWord transition initial (extendMarks w)
  let rr : (Fin K → Fin (n + 1)) → Nat → Fin (n + 1) → ℝ := fun w l => rates (states w l)
  let B : (Fin K → Fin (n + 1)) → Nat → Set (ℝ × ℝ) := fun w l =>
    {x | selection (List.ofFn (completedRates (rr w l))) x.2 = some (extendMarks w l).val}
  have hB : ∀ w l, MeasurableSet (B w l) := fun w l =>
    ((measurable_chooseAux _ _ _).comp (measurable_snd.mul_const _)) (measurableSet_singleton _)
  let E : (Fin K → Fin (n + 1)) → Set Streams := fun w =>
    parse ⁻¹' (Set.univ.pi (fun q : Fin K => B w (K - 1 - q)))
  have hE : ∀ w, MeasurableSet (E w) := fun w =>
    hparse (MeasurableSet.univ_pi (fun q => hB w _))
  let P := fun w => directPacketSpecification model (states w) (rr w) (extendMarks w)
    (fun l j => C.nonnegative _ j) (fun l => C.rates_eq _)
  -- The word branch law of the parsed primitive inputs.
  have hbranch : ∀ w, (iidStreams.restrict (E w)).map parse =
      rawWordLaw (fun l => directPacketInputs (rr w l) (extendMarks w l)) K := by
    intro w
    rw [← Measure.restrict_map hparse (MeasurableSet.univ_pi (fun q => hB w _)), hparse_law,
      ← rawWordLaw_restrict _ (fun _ => inferInstance) (B w) (hB w)]
    rfl
  have hclock : ∀ w l, (directPacketInputs (rr w l) (extendMarks w l)).map ((P w).clock l) =
      ENNReal.ofReal (completedRates (rr w l) (extendMarks w l) / (∑ j, completedRates (rr w l) j)) •
        expMeasure (∑ j, completedRates (rr w l) j) := fun w l =>
    direct_packet_clock_law (rr w l) (fun j => C.nonnegative _ j) (extendMarks w l)
  have hfin : ∀ w l, IsFiniteMeasure (directPacketInputs (rr w l) (extendMarks w l)) := by
    intro w l
    unfold directPacketInputs
    infer_instance
  have hmclock : ∀ w l, Measurable ((P w).clock l) := fun w l =>
    (measurable_exponentialClock _).comp measurable_fst
  have hholding : ∀ w, (rawWordLaw (fun l => directPacketInputs (rr w l) (extendMarks w l)) K).map
      (rawWordHoldings (P w).clock K) =
      targetWordLaw (fun l => completedRates (rr w l)) (extendMarks w) K := by
    intro w
    rw [raw_word_holding_law _ (hfin w) _ (hmclock w)]
    have h (k : Nat) : independentWordLaw (fun l =>
        (directPacketInputs (rr w l) (extendMarks w l)).map ((P w).clock l)) k =
        targetWordLaw (fun l => completedRates (rr w l)) (extendMarks w) k := by
      induction k with
      | zero => rfl
      | succ k ih => rw [independentWordLaw, targetWordLaw, ih, hclock w k]
    exact h K
  -- The words partition the probability space.
  have hmass : ∑ w, iidStreams (E w) = 1 := by
    have hw : ∀ w, iidStreams (E w) = pathWordWeight transition rates initial w := by
      intro w
      have h1 : iidStreams (E w) = ((iidStreams.restrict (E w)).map parse) univ := by
        rw [Measure.map_apply hparse MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
      rw [h1, hbranch, ← preimage_univ (f := rawWordHoldings (P w).clock K),
        ← Measure.map_apply (measurable_rawWordHoldings _ (hmclock w) K) MeasurableSet.univ,
        hholding, target_word_mass _ (fun l => completedRates_positive_total _)]
      unfold pathWordWeight
      apply Finset.prod_congr rfl
      intro q _
      simp only [extendMarks, q.isLt, dite_true, rr, states]
    simp_rw [hw]
    exact path_word_weights_normalize transition rates C.nonnegative K initial
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro w w' hww
    rw [Function.onFun, Set.disjoint_left]
    intro ω hω hω'
    apply hww
    apply words_eq_of_sequential_choice
    intro l hl hprev
    have hq : K - 1 - (⟨K - 1 - l, by omega⟩ : Fin K).val = l := by simp only; omega
    have h1 := (Set.mem_univ_pi.mp hω) ⟨K - 1 - l, by omega⟩
    have h2 := (Set.mem_univ_pi.mp hω') ⟨K - 1 - l, by omega⟩
    simp only [hq, B, mem_ofPred_eq] at h1 h2
    have hstates : states w l = states w' l :=
      stateAlongWord_congr transition initial _ _ l (extendMarks_agree w w' l (fun j hj hjK =>
        hprev j hj))
    have hmw : (extendMarks w l) = w ⟨l, hl⟩ := by simp [extendMarks, hl]
    have hmw' : (extendMarks w' l) = w' ⟨l, hl⟩ := by simp [extendMarks, hl]
    simp only [rr, hstates] at h1
    rw [h1, hmw, hmw'] at h2
    exact Fin.ext (Option.some_injective _ h2)
  -- Pointwise execution of the public driver on each word branch.
  let G : (Fin K → Fin (n + 1)) → Streams → X := fun w ω =>
    observable (holdingSimulationObservation model (states w) (rr w) (extendMarks w) start horizon
      fuel saveEvents (rawWordHoldings (P w).clock K (parse ω)))
  have hG : ∀ w, Measurable (G w) := fun w =>
    (hobs w).comp ((measurable_rawWordHoldings _ (hmclock w) K).comp hparse)
  have hFG : ∀ w, ∀ᵐ ω ∂iidStreams, ω ∈ E w →
      observable (observeRun (simulate realArithmetic (tapeSource ℝ) model .direct initial start
        horizon (streamTape (K + c) (K + d) ω) fuel saveEvents cap)) = G w ω := by
    intro w
    filter_upwards [iidStreams_ae_mem_Ioo] with ω hω hE
    have hgood : RawWordGood (P w).good K (parse ω) := by
      apply rawWordGood_of_index
      intro q
      have hb := (Set.mem_univ_pi.mp hE) q
      have hpq : parse ω q = (ω (.inr (K - 1 - q.val)), ω (.inl (K - 1 - q.val))) := by
        simp only [parse, directParse_eq]
      rw [hpq] at hb ⊢
      exact ⟨hω _, hω _, hb⟩
    have htape : streamTape (K + c) (K + d) ω =
        packetTapeFrom (P w).uniforms (P w).exponentials (rawChronological (1 / 2, 1 / 2) (parse ω))
          (streamTape c d (streamsDrop K K ω)) 0 K := by
      rw [directPacketTape_eq, streamTape_split]
      have hsrc : ∀ i : Fin K, rawChronological (1 / 2, 1 / 2) (parse ω) (0 + i.val) =
          (ω (.inr i), ω (.inl i)) := by
        intro i
        rw [zero_add]
        exact directParse_chronological K ω i i.isLt
      simp only [hsrc]
    have hinit : initial = states w 0 := rfl
    simp only [G]
    rw [htape, hinit, packet_driver_executes_from model .direct (states w) (rr w) (extendMarks w) (P w)
      (1 / 2, 1 / 2) (fun l => C.transition_eq _ _) start horizon hstart fuel cap saveEvents
      (parse ω) hgood (fun _ _ => Nat.zero_le _)]
  rw [iid_word_decomposition E hE hdisj hmass _ G hG hFG]
  unfold targetSimulationLaw
  congr 1
  funext w
  have h1 := Measure.map_map (μ := iidStreams.restrict (E w)) (hobs w)
    ((measurable_rawWordHoldings _ (hmclock w) K).comp hparse)
  have h2 := Measure.map_map (μ := iidStreams.restrict (E w))
    (measurable_rawWordHoldings _ (hmclock w) K) hparse
  rw [← h2, hbranch, hholding] at h1
  exact h1.symm

end JumpProcessesLean.Proofs
