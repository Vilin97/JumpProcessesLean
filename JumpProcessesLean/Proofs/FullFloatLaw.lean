import JumpProcessesLean.Proofs.FloatTrajectoryDistribution

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

def PrimitiveFloatInput (a : Algorithm) (n k : Nat) : Type :=
  match a with
  | .direct => Fin k → ℝ × ℝ
  | .nrm => NRMRawInput n k
  | .rssa => Fin k → RSSAStoppingInput (n + 1)

instance primitiveFloatInput_measurable (a : Algorithm) (n k : Nat) :
    MeasurableSpace (PrimitiveFloatInput a n k) := by
  cases a <;> dsimp only [PrimitiveFloatInput] <;> infer_instance

abbrev RSSARounding (n : Nat) := (k : Nat) → (p : RSSAStoppingInput (n + 1)) → Fin (p.1.1 + 1) → Binary64

def FloatRoundingSource (a : Algorithm) (n k : Nat) : Type :=
  match a with
  | .direct => (Nat → ℝ × ℝ → Binary64) × (Nat → ℝ × ℝ → Binary64)
  | .nrm => NRMRawInput n k → Nat → Fin (n + 1) → Binary64
  | .rssa => RSSARounding n × RSSARounding n × RSSARounding n

noncomputable def primitiveFloatWordInputs {n : Nat} (a : Algorithm)
    (rates lower upper : Nat → Fin (n + 1) → Binary64) (marks : Nat → Fin (n + 1)) (k : Nat) :
    Measure (PrimitiveFloatInput a n k) :=
  match a with
  | .direct => rawWordLaw (fun l => directPacketInputs (fun j => floatReal (rates l j)) (marks l)) k
  | .nrm => nrmRawPathLaw (fun l j => floatReal (rates l j)) marks k
  | .rssa => rawWordLaw (fun l => rssaPacketInputs (fun j => floatReal (rates l j))
      (fun j => floatReal (lower l j)) (fun j => floatReal (upper l j)) (marks l)) k

noncomputable def floatBranchRun {σ : Type} {n : Nat} (model : Model Binary64 σ) (initial : σ)
    (rates : Nat → Fin (n + 1) → Binary64) (marks : Nat → Fin (n + 1))
    (start horizon : Binary64) (fuel cap : Nat) (save : Bool) (a : Algorithm) :
    FloatRoundingSource a n (fuel + 1) → PrimitiveFloatInput a n (fuel + 1) →
      Except Error (TraceObservation Binary64 σ) :=
  match a with
  | .direct => fun q => directFloatRun model initial q.1 q.2 start horizon fuel cap save
  | .nrm => fun q => nrmFloatRun model initial rates marks fuel cap q start horizon save
  | .rssa => fun q => rssaFloatRun model initial q.1 q.2.1 q.2.2 start horizon fuel cap save

/-- A family of numerical input certificates, selected by algorithm. Its cases
are the input-only conditions checked by the native arithmetic refinements. -/
noncomputable def FloatBranchConditions {σ : Type} {n : Nat}
    (mf : Model Binary64 σ) (mr : Model ℝ σ) (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Fin (n + 1)) (rates lower upper : Nat → Fin (n + 1) → Binary64)
    (hm : ∀ l, mf.rates (states l) = Array.ofFn (rates l))
    (hb : ∀ l, mf.bounds (states l) = ⟨Array.ofFn (lower l), Array.ofFn (upper l)⟩)
    (hs : ∀ l, mf.transition (states l) (marks l).val = .ok (states (l + 1)))
    (start hf : Binary64) (sr hr ε d δ η : ℝ) (cacheBudget : Nat → ℝ)
    (fuel cap : Nat) (save : Bool) (a : Algorithm) :
    FloatRoundingSource a n (fuel + 1) → PrimitiveFloatInput a n (fuel + 1) → Prop :=
  match a with
  | .direct => fun q p => DirectTrajectoryConditions mf mr htransition states (fun l => (marks l).val)
      (fun l => Array.ofFn (rates l)) hm hs q.1 q.2 (rawChronological (1 / 2, 1 / 2) p)
      start hf sr hr ε d δ η fuel cap save
  | .nrm => fun q p => NRMTrajectoryConditions mf mr htransition states marks rates (q p)
      (nrmRawExponentials p) hm hs start hf sr hr δ cacheBudget fuel cap save
  | .rssa => fun q p => RSSATrajectoryConditions mf mr htransition states (fun l => (marks l).val)
      (fun l => Array.ofFn (rates l)) (fun l => ⟨Array.ofFn (lower l), Array.ofFn (upper l)⟩) hm hb hs
      q.1 q.2.1 q.2.2 (rawChronological ⟨(0, 0), (fun _ => 1 / 2, fun _ => (1 / 2, 1 / 2))⟩ p)
      start hf sr hr ε d δ η fuel cap save

/-- Algorithm-uniform word theorem with numerical input hypotheses. The three
cases invoke independently checked primitive-input distribution proofs. -/
theorem float_branch_joint_tail_approx {σ ι : Type} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {n : Nat} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Fin (n + 1)) (rates lower upper : Nat → Fin (n + 1) → Binary64)
    (hm : ∀ l, mf.rates (states l) = Array.ofFn (rates l))
    (hb : ∀ l, mf.bounds (states l) = ⟨Array.ofFn (lower l), Array.ofFn (upper l)⟩)
    (hs : ∀ l, mf.transition (states l) (marks l).val = .ok (states (l + 1)))
    (hpos : ∀ l j, 0 < floatReal (rates l j))
    (hbounds : ∀ l j, 0 ≤ floatReal (lower l j) ∧ floatReal (lower l j) ≤ floatReal (rates l j) ∧
      floatReal (rates l j) ≤ floatReal (upper l j))
    (start hf : Binary64) (sr hr ε d δ η εobs : ℝ) (cacheBudget : Nat → ℝ)
    (fuel cap : Nat) (save : Bool) (a : Algorithm) (q : FloatRoundingSource a n (fuel + 1))
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (hεobs : 0 ≤ εobs)
    (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ εobs ∧ If f = I r)
    (hM : Measurable (fun ts =>
      let r := holdingSimulationObservation mr states (fun l j => floatReal (rates l j)) marks sr hr fuel save ts
      (T r, I r)))
    (bad : Set (PrimitiveFloatInput a n (fuel + 1))) (hbad : MeasurableSet bad)
    (hgood : ∀ p ∉ bad, FloatBranchConditions mf mr htransition states marks rates lower upper hm hb hs
      start hf sr hr ε d δ η cacheBudget fuel cap save a q p)
    (i : ι) (t : ℝ) :
    let μ := primitiveFloatWordInputs a rates lower upper marks (fuel + 1)
    let ν := (targetWordLaw (fun l j => floatReal (rates l j)) marks (fuel + 1)).map
      (fun ts =>
        let r := holdingSimulationObservation mr states (fun l j => floatReal (rates l j)) marks sr hr fuel save ts
        (T r, I r))
    ν (jointTail (t + εobs) i) ≤ μ {p | t < Tf (floatBranchRun mf (states 0) rates marks start hf fuel cap save a q p) ∧
      If (floatBranchRun mf (states 0) rates marks start hf fuel cap save a q p) = i} + μ bad ∧
    μ {p | t < Tf (floatBranchRun mf (states 0) rates marks start hf fuel cap save a q p) ∧
      If (floatBranchRun mf (states 0) rates marks start hf fuel cap save a q p) = i} ≤ ν (jointTail (t - εobs) i) + μ bad := by
  have hA l : 0 < ∑ j, floatReal (rates l j) := Finset.sum_pos (fun j _ => hpos l j) Finset.univ_nonempty
  cases a with
  | direct =>
    exact direct_float_simulation_joint_tail_approx mf mr htransition states marks rates hm hs
      (fun l j => (hpos l j).le) hA q.1 q.2 start hf sr hr ε d δ η εobs fuel cap save
      T Tf I If hεobs hobs hM bad hbad hgood i t
  | nrm =>
    exact nrm_float_simulation_joint_tail_approx mf mr htransition states marks rates hm hs hpos fuel cap save
      q start hf sr hr δ εobs cacheBudget T Tf I If hεobs hobs hM bad hbad hgood i t
  | rssa =>
    exact rssa_float_simulation_joint_tail_approx mf mr htransition states marks rates lower upper hm hb hs
      hA hbounds q.1 q.2.1 q.2.2 start hf sr hr ε d δ η εobs fuel cap save
      T Tf I If hεobs hobs hM bad hbad hgood i t

structure FloatModelConsistency {σ : Type} {n : Nat} (model : Model Binary64 σ)
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → Binary64) : Prop where
  rates_eq : ∀ x, model.rates x = Array.ofFn (rates x)
  bounds_eq : ∀ x, model.bounds x = ⟨Array.ofFn (lower x), Array.ofFn (upper x)⟩
  transition_eq : ∀ x j, model.transition x j.val = .ok (transition x j)

noncomputable def floatWordConditions {σ : Type} {n : Nat}
    (mf : Model Binary64 σ) (mr : Model ℝ σ) (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition rates lower upper) (initial : σ)
    (start hf : Binary64) (sr hr ε d δ η : ℝ) (cacheBudget : Nat → ℝ)
    (fuel cap : Nat) (save : Bool) (a : Algorithm) (word : Fin (fuel + 1) → Fin (n + 1))
    (q : FloatRoundingSource a n (fuel + 1)) (p : PrimitiveFloatInput a n (fuel + 1)) : Prop :=
  let marks := extendMarks word
  let states := stateAlongWord transition initial marks
  FloatBranchConditions mf mr htransition states marks (fun l => rates (states l))
    (fun l => lower (states l)) (fun l => upper (states l))
    (fun l => CF.rates_eq (states l)) (fun l => CF.bounds_eq (states l))
    (fun l => CF.transition_eq (states l) (marks l))
    start hf sr hr ε d δ η cacheBudget fuel cap save a q p

noncomputable def floatFullTailProbability {σ ι : Type} {n : Nat}
    (mf : Model Binary64 σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → Binary64) (initial : σ)
    (start hf : Binary64) (fuel cap : Nat) (save : Bool) (a : Algorithm)
    (rounding : (Fin (fuel + 1) → Fin (n + 1)) → FloatRoundingSource a n (fuel + 1))
    (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (If : Except Error (TraceObservation Binary64 σ) → ι) (i : ι) (t : ℝ) : ℝ≥0∞ :=
  ∑ word : Fin (fuel + 1) → Fin (n + 1),
    let marks := extendMarks word
    let states := stateAlongWord transition initial marks
    let μ := primitiveFloatWordInputs a (fun l => rates (states l)) (fun l => lower (states l))
      (fun l => upper (states l)) marks (fuel + 1)
    μ {p | t < Tf (floatBranchRun mf initial (fun l => rates (states l)) marks start hf fuel cap save a (rounding word) p) ∧
      If (floatBranchRun mf initial (fun l => rates (states l)) marks start hf fuel cap save a (rounding word) p) = i}

noncomputable def floatFullBadMass {σ : Type} {n : Nat}
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → Binary64)
    (initial : σ) (fuel : Nat) (a : Algorithm)
    (bad : (Fin (fuel + 1) → Fin (n + 1)) → Set (PrimitiveFloatInput a n (fuel + 1))) : ℝ≥0∞ :=
  ∑ word : Fin (fuel + 1) → Fin (n + 1),
    let marks := extendMarks word
    let states := stateAlongWord transition initial marks
    primitiveFloatWordInputs a (fun l => rates (states l)) (fun l => lower (states l))
      (fun l => upper (states l)) marks (fuel + 1) (bad word)

/-- End-to-end floating simulation approximation, summed over every state-dependent
reaction word. All three FloatLib algorithms approximate the same REAL native
simulation law. Numerical/source certificates, race/CDF/acceptance and horizon
margins are hypotheses on inputs; no sampler law or output agreement is assumed.

This whole-trajectory theorem uses positive decoded rates. The exact real theorem
also covers inactive and absorbing channels. `β` explicitly retains every failed
certificate or capped RSSA branch; it is not conditioned away. -/
theorem float_simulations_approximate_same_real_law {σ ι : Type} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {n : Nat} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition rates lower upper)
    (CR : ModelConsistency mr transition (fun x j => floatReal (rates x j))
      (fun x j => floatReal (lower x j)) (fun x j => floatReal (upper x j)))
    (hpos : ∀ x j, 0 < floatReal (rates x j)) (initial : σ)
    (start hf : Binary64) (sr hr ε d δ η εobs : ℝ) (hstart : sr < hr)
    (cacheBudget : Nat → ℝ) (fuel cap : Nat) (save : Bool) (a b : Algorithm)
    (rounding : (Fin (fuel + 1) → Fin (n + 1)) → FloatRoundingSource a n (fuel + 1))
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (hεobs : 0 ≤ εobs)
    (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ εobs ∧ If f = I r)
    (hM : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts =>
        let r := holdingSimulationObservation mr states (fun l j => floatReal (rates (states l) j)) marks sr hr fuel save ts
        (T r, I r)))
    (bad : (Fin (fuel + 1) → Fin (n + 1)) → Set (PrimitiveFloatInput a n (fuel + 1)))
    (hbad : ∀ word, MeasurableSet (bad word))
    (hgood : ∀ word p, p ∉ bad word → floatWordConditions mf mr htransition transition rates lower upper CF initial
      start hf sr hr ε d δ η cacheBudget fuel cap save a word (rounding word) p)
    (i : ι) (t : ℝ) :
    let ν := nativeSimulationLaw mr transition (fun x j => floatReal (rates x j))
      (fun x j => floatReal (lower x j)) (fun x j => floatReal (upper x j)) CR initial sr hr fuel save (fun r => (T r, I r)) b
    let β := floatFullBadMass transition rates lower upper initial fuel a bad
    ν (jointTail (t + εobs) i) ≤ floatFullTailProbability mf transition rates lower upper initial
      start hf fuel cap save a rounding Tf If i t + β ∧
    floatFullTailProbability mf transition rates lower upper initial start hf fuel cap save a rounding Tf If i t ≤
      ν (jointTail (t - εobs) i) + β := by
  dsimp only
  rw [native_simulation_law_eq_target mr transition (fun x j => floatReal (rates x j))
    (fun x j => floatReal (lower x j)) (fun x j => floatReal (upper x j)) CR initial sr hr hstart
    fuel save (fun r => (T r, I r)) hM b]
  have hA x : 0 < ∑ j, floatReal (rates x j) := Finset.sum_pos (fun j _ => hpos x j) Finset.univ_nonempty
  have hcomplete x : completedRates (fun j => floatReal (rates x j)) = fun j => floatReal (rates x j) := by
    simp only [completedRates, hA, ite_true]
  unfold targetSimulationLaw
  rw [Measure.sum_apply _ (by unfold jointTail; measurability),
    Measure.sum_apply _ (by unfold jointTail; measurability)]
  simp only [tsum_fintype]
  simp_rw [hcomplete]
  have hword (word : Fin (fuel + 1) → Fin (n + 1)) :=
    float_branch_joint_tail_approx mf mr htransition (stateAlongWord transition initial (extendMarks word))
      (extendMarks word) (fun l => rates (stateAlongWord transition initial (extendMarks word) l))
      (fun l => lower (stateAlongWord transition initial (extendMarks word) l))
      (fun l => upper (stateAlongWord transition initial (extendMarks word) l))
      (fun l => CF.rates_eq _) (fun l => CF.bounds_eq _) (fun l => CF.transition_eq _ _)
      (fun l => hpos _) (fun l => CR.bounds_valid _) start hf sr hr ε d δ η εobs cacheBudget
      fuel cap save a (rounding word) T Tf I If hεobs hobs (hM word) (bad word) (hbad word)
      (hgood word) i t
  constructor
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun word _ => (hword word).1)
    simpa only [Finset.sum_add_distrib, floatFullTailProbability, floatFullBadMass, stateAlongWord] using h
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun word _ => (hword word).2)
    simpa only [Finset.sum_add_distrib, floatFullTailProbability, floatFullBadMass, stateAlongWord] using h

lemma raw_word_mass_from_clock_law {γ : Type} [MeasurableSpace γ] {n : Nat}
    (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (inputs : Nat → Measure γ) (hf : ∀ l, IsFiniteMeasure (inputs l))
    (clock : Nat → γ → ℝ) (hm : ∀ l, Measurable (clock l))
    (hlaw : ∀ l, (inputs l).map (clock l) =
      ENNReal.ofReal (rates l (marks l) / (∑ j, rates l j)) • expMeasure (∑ j, rates l j)) (k : Nat) :
    rawWordLaw inputs k univ = targetWordLaw rates marks k univ := by
  have ht (k : Nat) : independentWordLaw (fun l => (inputs l).map (clock l)) k = targetWordLaw rates marks k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [independentWordLaw, targetWordLaw, ih, hlaw k]
  have h := raw_word_holding_law inputs hf clock hm k
  rw [ht] at h
  have he := congrArg (fun μ : Measure (Fin k → ℝ) => μ univ) h
  rw [Measure.map_apply (measurable_rawWordHoldings clock hm k) MeasurableSet.univ, preimage_univ] at he
  exact he

/-- Primitive branches carry their actual word probability, without normalization. -/
theorem primitive_float_word_mass {n : Nat} (a : Algorithm)
    (rates lower upper : Nat → Fin (n + 1) → Binary64)
    (hpos : ∀ l j, 0 < floatReal (rates l j))
    (hb : ∀ l j, 0 ≤ floatReal (lower l j) ∧ floatReal (lower l j) ≤ floatReal (rates l j) ∧
      floatReal (rates l j) ≤ floatReal (upper l j)) (marks : Nat → Fin (n + 1)) (k : Nat) :
    primitiveFloatWordInputs a rates lower upper marks k univ =
      targetWordLaw (fun l j => floatReal (rates l j)) marks k univ := by
  let rr := fun l j => floatReal (rates l j)
  let lo := fun l j => floatReal (lower l j)
  let up := fun l j => floatReal (upper l j)
  have hA l : 0 < ∑ j, rr l j := Finset.sum_pos (fun j _ => hpos l j) Finset.univ_nonempty
  have hc l : completedRates (rr l) = rr l := by simp only [completedRates, hA, ite_true]
  cases a with
  | direct =>
    apply raw_word_mass_from_clock_law rr marks (fun l => directPacketInputs (rr l) (marks l))
      (fun l => by unfold directPacketInputs; infer_instance)
      (fun l p => exponentialClock (∑ j, rr l j) p.1)
      (fun l => (measurable_exponentialClock _).comp measurable_fst)
    intro l
    simpa only [hc] using direct_packet_clock_law (rr l) (fun j => (hpos l j).le) (marks l)
  | nrm =>
    have h := nrm_raw_holding_times_law rr (fun l j => (hpos l j).le) marks k
    have he := congrArg (fun μ : Measure (Fin k → ℝ) => μ univ) h
    rw [Measure.map_apply ((measurable_nrmRawHistory _ _ _).fst) MeasurableSet.univ, preimage_univ] at he
    exact he
  | rssa =>
    apply raw_word_mass_from_clock_law rr marks (fun l => rssaPacketInputs (rr l) (lo l) (up l) (marks l))
      (fun l => rssa_packet_finite _ _ _ (hb l) _)
      (fun l => rssaStoppingTime (List.ofFn (completedUpper (rr l) (up l))))
      (fun l => measurable_rssaStoppingTime _)
    intro l
    simpa only [hc] using rssa_packet_clock_law (rr l) (lo l) (up l) (hb l) (marks l)

/-- The bad mass in the complete approximation theorem is a genuine probability
at most one, formed from all primitive word branches. -/
theorem float_full_bad_mass_le_one {σ : Type} {n : Nat}
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → Binary64)
    (hpos : ∀ x j, 0 < floatReal (rates x j))
    (hb : ∀ x j, 0 ≤ floatReal (lower x j) ∧ floatReal (lower x j) ≤ floatReal (rates x j) ∧
      floatReal (rates x j) ≤ floatReal (upper x j))
    (initial : σ) (fuel : Nat) (a : Algorithm)
    (bad : (Fin (fuel + 1) → Fin (n + 1)) → Set (PrimitiveFloatInput a n (fuel + 1))) :
    floatFullBadMass transition rates lower upper initial fuel a bad ≤ 1 := by
  unfold floatFullBadMass
  have hw (word : Fin (fuel + 1) → Fin (n + 1)) :
      primitiveFloatWordInputs a (fun l => rates (stateAlongWord transition initial (extendMarks word) l))
        (fun l => lower (stateAlongWord transition initial (extendMarks word) l))
        (fun l => upper (stateAlongWord transition initial (extendMarks word) l))
        (extendMarks word) (fuel + 1) (bad word) ≤
      pathWordWeight transition (fun x j => floatReal (rates x j)) initial word := by
    apply (measure_mono (subset_univ _)).trans
    rw [primitive_float_word_mass a _ _ _ (fun l => hpos _) (fun l => hb _)]
    have hA l : 0 < ∑ j, floatReal (rates (stateAlongWord transition initial (extendMarks word) l) j) :=
      Finset.sum_pos (fun j _ => hpos _ j) Finset.univ_nonempty
    rw [target_word_mass _ hA]
    have hc x : completedRates (fun j => floatReal (rates x j)) = fun j => floatReal (rates x j) := by
      have hh : 0 < ∑ j, floatReal (rates x j) := Finset.sum_pos (fun j _ => hpos x j) Finset.univ_nonempty
      simp only [completedRates, hh, ite_true]
    unfold pathWordWeight
    simp_rw [hc]
    apply le_of_eq
    apply Finset.prod_congr rfl
    intro q _
    simp only [extendMarks, q.isLt, dite_true]
  calc
    _ ≤ ∑ word, pathWordWeight transition (fun x j => floatReal (rates x j)) initial word :=
      Finset.sum_le_sum (fun word _ => hw word)
    _ = 1 := path_word_weights_normalize transition (fun x j => floatReal (rates x j))
      (fun x j => (hpos x j).le) (fuel + 1) initial

end JumpProcessesLean.Proofs
