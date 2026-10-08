import JumpProcessesLean.Proofs.RSSAIID
import JumpProcessesLean.Proofs.FullFloatLaw

/-!
# FloatLib simulations coupled to the IID streams

The real simulator reads the IID streams through `streamTape`. The FloatLib
simulator reads the same streams through fixed rounding maps: the `i`th float uniform
is `ρu (U i)` and the `i`th float exponential is `ρe (V i)`, where the real exponential
is `-log (V i)`. Nothing depends on the reaction word. On an explicit event, defined
by the numerical input certificates along the realized real word, the actual public
float simulator stays trace-close to the actual public real simulator. The failure
event's outer probability bounds the distance to the exact target law.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- FloatLib tape read from the IID streams through fixed rounding maps. -/
noncomputable def floatStreamTape (ρu ρe : ℝ → Binary64) (a b : ℕ) (ω : Streams) : Tape Binary64 :=
  ⟨List.ofFn (fun i : Fin a => ρu (ω (.inl i))), List.ofFn (fun i : Fin b => ρe (ω (.inr i)))⟩

/-- Float packet tapes followed by an arbitrary unread tape. -/
def floatPacketTapeFrom {γ : Type} (u e : Nat → γ → List Binary64) (source : Nat → γ)
    (tail : Tape Binary64) : Nat → Nat → Tape Binary64
  | _, 0 => tail
  | k, count + 1 =>
    let rest := floatPacketTapeFrom u e source tail (k + 1) count
    ⟨u k (source k) ++ rest.uniforms, e k (source k) ++ rest.exponentials⟩

/-- Whole native Direct/RSSA float composition, with any unread tape suffix. -/
theorem float_packet_trajectory_close_from {σ γ : Type} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (algorithm : Algorithm) (hnrm : algorithm ≠ .nrm)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Nat)
    (clock : Nat → Binary64 → γ → Binary64) (u e : Nat → γ → List Binary64)
    (realClock : Nat → γ → ℝ) (source : Nat → γ) (tail : Tape Binary64)
    (start hf : Binary64) (sr hr ε d δ : ℝ) (fuel cap : Nat) (save : Bool)
    (P : LocalPacketRefinement mf algorithm states marks clock u e realClock source start cap fuel d)
    (hstate : ∀ k, mf.transition (states k) (marks k) = .ok (states (k + 1)))
    (hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true) (hstart : binary64Arithmetic.lt start hf = true)
    (hhf : ExecFloat.Binary.isFinite hf = true) (hh : |floatReal hf - hr| ≤ δ)
    (h0 : |floatReal start - sr| ≤ ε) (hd : 0 ≤ d)
    (hbudget : ε + ((fuel + 1 : Nat) : ℝ) * d ≤ δ)
    (hmargin : ∀ k, k ≤ fuel → 2 * δ < |realTimeSchedule realClock source sr (k + 1) - hr|) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf algorithm (states 0) start hf
        (floatPacketTapeFrom u e source tail 0 (fuel + 1)) fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule realClock source sr) marks 0 (fuel + 1))) := by
  let tf := floatTimeSchedule clock source start
  let tr := realTimeSchedule realClock source sr
  let tape := floatPacketTapeFrom u e source tail
  have hbound (k : Nat) (hk : k ≤ fuel + 1) : ε + (k : ℝ) * d ≤ δ := by
    have hcast : (k : ℝ) ≤ ((fuel + 1 : Nat) : ℝ) := by exact_mod_cast hk
    exact (add_le_add (le_refl ε) (mul_le_mul_of_nonneg_right hcast hd)).trans hbudget
  apply simulate_float_schedule_close (tapeSource Binary64) mf mr algorithm htransition states tf tr marks
    hf hr δ fuel cap save tape (fun k count => tape (k + 1) count) (fun _ => none)
    (tape 0 (fuel + 1))
  · cases algorithm with
    | direct => rfl
    | rssa => rfl
    | nrm => exact (hnrm rfl).elim
  · exact hvalid
  · exact hstart
  · exact hhf
  · exact hh
  · exact h0.trans (by simpa only [Nat.cast_zero, zero_mul, add_zero] using hbound 0 (by omega))
  · intro k count hk
    change sampleEvent _ _ _ _ _ _ _ (floatPacketTapeFrom u e source tail k (count + 1)) _ = _
    rw [floatPacketTapeFrom]
    exact P.execute k (by omega) _ _
  · exact hstate
  · intro k count hk
    cases algorithm <;> rfl
  · exact P.finite
  · exact P.increasing
  · intro k hk
    change tr k ≤ tr k + realClock k (source k)
    exact le_add_of_nonneg_right (P.positive k hk)
  · intro k hk
    exact (packet_accumulated_time_error mf algorithm states marks clock u e realClock source start sr
      cap fuel d ε P h0 (k + 1) (by omega)).trans (hbound (k + 1) (by omega))
  · exact hmargin

/-! ### Comparison with a word decomposition of the target law -/

lemma outer_measure_inter_iUnion {ι : Type} [Countable ι] (E : ι → Set Streams)
    (hE : ∀ w, MeasurableSet (E w)) (hd : Pairwise (Function.onFun Disjoint E)) (A : Set Streams) :
    iidStreams (A ∩ ⋃ w, E w) = ∑' w, iidStreams (A ∩ E w) := by
  rw [← Measure.restrict_apply' (MeasurableSet.iUnion hE), Measure.restrict_iUnion hd hE,
    Measure.sum_apply_of_countable]
  congr 1
  funext w
  rw [Measure.restrict_apply' (hE w)]

/-- A coupled process that agrees, on every word branch and outside a failure event,
with a measurable formula whose branch laws sum to `target`, has joint tails within
the outer probability of failure. No measurability of the coupled process is used. -/
theorem word_coupling_tail_bounds {ι κ Y : Type} [Fintype ι] [MeasurableSpace κ]
    [MeasurableSingletonClass κ]
    (E : ι → Set Streams) (hE : ∀ w, MeasurableSet (E w)) (hd : Pairwise (Function.onFun Disjoint E))
    (hmass : ∑ w, iidStreams (E w) = 1)
    (G : ι → Streams → ℝ × κ) (hG : ∀ w, Measurable (G w))
    (target : Measure (ℝ × κ))
    (htarget : target = Measure.sum (fun w => (iidStreams.restrict (E w)).map (G w)))
    (Ff : Streams → Y) (Tf : Y → ℝ) (If : Y → κ) (good : Set Streams) (ε : ℝ)
    (hclose : ∀ w, ∀ ω ∈ E w ∩ good, |Tf (Ff ω) - (G w ω).1| ≤ ε ∧ If (Ff ω) = (G w ω).2)
    (i : κ) (t : ℝ) :
    target (jointTail (t + ε) i) ≤ iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} + iidStreams goodᶜ ∧
    iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} ≤ target (jointTail (t - ε) i) + iidStreams goodᶜ := by
  have hJ : ∀ s : ℝ, MeasurableSet (jointTail s i) := fun s => by unfold jointTail; measurability
  have hunion : iidStreams (⋃ w, E w)ᶜ = 0 := by
    rw [measure_compl (MeasurableSet.iUnion hE) (measure_ne_top _ _), measure_iUnion hd hE,
      tsum_fintype, hmass, measure_univ, tsub_self]
  have htsum : ∀ s : ℝ, target (jointTail s i) = ∑ w, iidStreams (G w ⁻¹' jointTail s i ∩ E w) := by
    intro s
    rw [htarget, Measure.sum_apply _ (hJ s), tsum_fintype]
    congr 1
    funext w
    rw [Measure.map_apply (hG w) (hJ s), Measure.restrict_apply' (hE w)]
  let F := {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i}
  have hsplit : ∀ A : Set Streams, iidStreams A = ∑ w, iidStreams (A ∩ E w) := by
    intro A
    have h := outer_measure_inter_iUnion E hE hd A
    rw [tsum_fintype] at h
    rw [← h]
    apply le_antisymm
    · calc iidStreams A ≤ iidStreams (A ∩ ⋃ w, E w) + iidStreams (A \ ⋃ w, E w) :=
            measure_le_inter_add_diff _ _ _
        _ = iidStreams (A ∩ ⋃ w, E w) := by
            have hz : iidStreams (A \ ⋃ w, E w) = 0 := measure_mono_null (fun ω hω => hω.2) hunion
            rw [hz, add_zero]
    · exact measure_mono inter_subset_left
  have hgood_sum : ∑ w, iidStreams (goodᶜ ∩ E w) ≤ iidStreams goodᶜ := by
    rw [← hsplit]
  constructor
  · rw [htsum]
    calc ∑ w, iidStreams (G w ⁻¹' jointTail (t + ε) i ∩ E w)
        ≤ ∑ w, (iidStreams (F ∩ E w) + iidStreams (goodᶜ ∩ E w)) := by
          apply Finset.sum_le_sum
          intro w _
          apply (measure_mono _).trans (measure_union_le _ _)
          intro ω ⟨hJω, hEω⟩
          by_cases hg : ω ∈ good
          · left
            have hc := hclose w ω ⟨hEω, hg⟩
            simp only [jointTail, mem_preimage, mem_setOf_eq] at hJω
            refine ⟨⟨?_, hc.2.trans hJω.2⟩, hEω⟩
            have := abs_le.mp hc.1
            linarith [hJω.1]
          · exact Or.inr ⟨hg, hEω⟩
      _ = ∑ w, iidStreams (F ∩ E w) + ∑ w, iidStreams (goodᶜ ∩ E w) := Finset.sum_add_distrib
      _ ≤ iidStreams F + iidStreams goodᶜ := by rw [← hsplit F]; exact add_le_add le_rfl hgood_sum
  · rw [htsum, hsplit F]
    calc ∑ w, iidStreams (F ∩ E w)
        ≤ ∑ w, (iidStreams (G w ⁻¹' jointTail (t - ε) i ∩ E w) + iidStreams (goodᶜ ∩ E w)) := by
          apply Finset.sum_le_sum
          intro w _
          apply (measure_mono _).trans (measure_union_le _ _)
          intro ω ⟨hFω, hEω⟩
          by_cases hg : ω ∈ good
          · left
            have hc := hclose w ω ⟨hEω, hg⟩
            refine ⟨?_, hEω⟩
            simp only [jointTail, mem_preimage, mem_setOf_eq]
            have := abs_le.mp hc.1
            exact ⟨by linarith [hFω.1], hc.2.symm.trans hFω.2⟩
          · exact Or.inr ⟨hg, hEω⟩
      _ = ∑ w, iidStreams (G w ⁻¹' jointTail (t - ε) i ∩ E w) + ∑ w, iidStreams (goodᶜ ∩ E w) :=
          Finset.sum_add_distrib
      _ ≤ _ := add_le_add le_rfl hgood_sum

/-! ### Schedule bookkeeping -/

lemma floatStreamTape_split (ρu ρe : ℝ → Binary64) (a b c d : ℕ) (ω : Streams) :
    floatStreamTape ρu ρe (a + c) (b + d) ω =
      ⟨List.ofFn (fun i : Fin a => ρu (ω (.inl i))) ++
          (floatStreamTape ρu ρe c d (streamsDrop a b ω)).uniforms,
        List.ofFn (fun i : Fin b => ρe (ω (.inr i))) ++
          (floatStreamTape ρu ρe c d (streamsDrop a b ω)).exponentials⟩ := by
  simp only [floatStreamTape, List.ofFn_add, streamsDrop, Sum.map_inl, Sum.map_inr]
  rfl

lemma floatPacketTapeFrom_single {γ : Type} (g h : γ → Binary64) (source : Nat → γ)
    (tail : Tape Binary64) (k count : Nat) :
    floatPacketTapeFrom (fun _ p => [g p]) (fun _ p => [h p]) source tail k count =
      ⟨List.ofFn (fun i : Fin count => g (source (k + i))) ++ tail.uniforms,
        List.ofFn (fun i : Fin count => h (source (k + i))) ++ tail.exponentials⟩ := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
    rw [floatPacketTapeFrom, ih (k + 1)]
    simp only [List.ofFn_succ, Fin.val_zero, add_zero, Fin.val_succ, List.cons_append,
      List.nil_append]
    simp only [Nat.add_assoc, Nat.add_comm 1]

lemma realTimeSchedule_congr {γ : Type} (c c' : Nat → γ → ℝ) (source : Nat → γ) (start : ℝ)
    (L : Nat) (h : ∀ l, l < L → c l (source l) = c' l (source l)) :
    ∀ l, l ≤ L → realTimeSchedule c source start l = realTimeSchedule c' source start l := by
  intro l
  induction l with
  | zero => intro _; rfl
  | succ l ih =>
    intro hl
    rw [realTimeSchedule, realTimeSchedule, ih (by omega), h l (by omega)]

lemma scheduledEvents_congr {α : Type} (t t' : Nat → α) (marks : Nat → Nat) :
    ∀ count k, (∀ l, k < l → l ≤ k + count → t l = t' l) →
      scheduledEvents t marks k count = scheduledEvents t' marks k count := by
  intro count
  induction count with
  | zero => intro k _; rfl
  | succ count ih =>
    intro k h
    rw [scheduledEvents, scheduledEvents, h (k + 1) (by omega) (by omega),
      ih (k + 1) (fun l hl hl' => h l (by omega) (by omega))]

/-! ### Direct -/

section DirectFloat

variable {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
  (htransition : ∀ x i, mf.transition x i = mr.transition x i)
  (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
  (CF : FloatModelConsistency mf transition ratesF lowerF upperF) (initial : σ)
  (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ) (fuel cap : ℕ) (save : Bool)

/-- Numerical certificate event of the coupled Direct simulations: the realized
real reaction word carries the Direct trajectory certificate. -/
noncomputable def directFloatGood : Set Streams :=
  {ω | (∀ x, ω x ∈ Ioo (0 : ℝ) 1) ∧ ∃ w : Fin (fuel + 1) → Fin (n + 1),
    ω ∈ directWordEvent transition (fun x j => floatReal (ratesF x j)) initial w ∧
    DirectTrajectoryConditions mf mr htransition (stateAlongWord transition initial (extendMarks w))
      (fun l => (extendMarks w l).val)
      (fun l => Array.ofFn (ratesF (stateAlongWord transition initial (extendMarks w) l)))
      (fun l => CF.rates_eq _) (fun l => CF.transition_eq _ _) (fun _ p => ρe p.1) (fun _ p => ρu p.2)
      (rawChronological (1 / 2, 1 / 2) (directParse (fuel + 1) ω)) start hf sr hr ε d δ η fuel cap save}

end DirectFloat

lemma sum_floatReal_ofFn {n : ℕ} (f : Fin n → Binary64) :
    ((Array.ofFn f).toList.map floatReal).sum = ∑ j, floatReal (f j) := by
  rw [Array.toList_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

lemma direct_real_clock_eq_word {σ : Type} {n : ℕ} (transition : σ → Fin (n + 1) → σ)
    (ratesF : σ → Fin (n + 1) → Binary64) (initial : σ) {K : ℕ} (w : Fin K → Fin (n + 1)) (l : ℕ)
    (hA : 0 < ((Array.ofFn (ratesF (stateAlongWord transition initial (extendMarks w) l))).toList.map
      floatReal).sum) (p : ℝ × ℝ) :
    directRealClock (fun l => Array.ofFn (ratesF (stateAlongWord transition initial (extendMarks w) l))) l p =
      directWordClock transition (fun x j => floatReal (ratesF x j)) initial w l p := by
  have hsum : ((Array.ofFn (ratesF (stateAlongWord transition initial (extendMarks w) l))).toList.map
      floatReal).sum = ∑ j, floatReal (ratesF (stateAlongWord transition initial (extendMarks w) l) j) :=
    sum_floatReal_ofFn _
  rw [hsum] at hA
  simp only [directRealClock, directWordClock, completedRates, hA, ite_true, hsum]

/-- On the Direct certificate event, the public FloatLib Direct simulator is trace-close
to the public real Direct simulator, both reading the same IID streams. -/
theorem direct_float_iid_close {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (c e : ℕ) (ω : Streams)
    (hω : ω ∈ directFloatGood mf mr htransition transition ratesF lowerF upperF CF initial ρu ρe start hf
      sr hr ε d δ η fuel cap save) :
    ∃ w : Fin (fuel + 1) → Fin (n + 1),
      ω ∈ directWordEvent transition (fun x j => floatReal (ratesF x j)) initial w ∧
      observeRun (simulate realArithmetic (tapeSource ℝ) mr .direct initial sr hr
        (streamTape (fuel + 1 + c) (fuel + 1 + e) ω) fuel save cap) =
        holdingSimulationObservation mr (stateAlongWord transition initial (extendMarks w))
          (fun l j => floatReal (ratesF (stateAlongWord transition initial (extendMarks w) l) j))
          (extendMarks w) sr hr fuel save
          (rawWordHoldings (directWordClock transition (fun x j => floatReal (ratesF x j)) initial w)
            (fuel + 1) (directParse (fuel + 1) ω)) ∧
      TraceClose δ
        (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .direct initial start hf
          (floatStreamTape ρu ρe (fuel + 1 + c) (fuel + 1 + e) ω) fuel save cap))
        (observeRun (simulate realArithmetic (tapeSource ℝ) mr .direct initial sr hr
          (streamTape (fuel + 1 + c) (fuel + 1 + e) ω) fuel save cap)) := by
  obtain ⟨hcoord, w, hE, hcert⟩ := hω
  let states := stateAlongWord transition initial (extendMarks w)
  let rates := fun l => Array.ofFn (ratesF (states l))
  let source := rawChronological (1 / 2, 1 / 2) (directParse (fuel + 1) ω)
  have hreal := direct_stream_driver_executes mr transition (fun x j => floatReal (ratesF x j))
    (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)) CR initial sr hr hsr fuel
    cap save c e w ω hcoord hE
  refine ⟨w, hE, hreal, ?_⟩
  have hA : ∀ l, l ≤ fuel → 0 < ∑ j, floatReal (ratesF (states l) j) := by
    intro l hl
    have h := hcert.hA l hl
    rwa [sum_floatReal_ofFn] at h
  -- The real public run is the replay of the real certificate schedule.
  have hreplay : holdingSimulationObservation mr states (fun l j => floatReal (ratesF (states l) j))
      (extendMarks w) sr hr fuel save
      (rawWordHoldings (directWordClock transition (fun x j => floatReal (ratesF x j)) initial w)
        (fuel + 1) (directParse (fuel + 1) ω)) =
      replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (directRealClock rates) source sr)
          (fun l => (extendMarks w l).val) 0 (fuel + 1)) := by
    rw [← packet_real_replay_eq_holdings mr states (fun l j => floatReal (ratesF (states l) j))
      (extendMarks w) _ (1 / 2, 1 / 2) sr hr fuel save hA]
    unfold packetRealReplay
    congr 1
    apply scheduledEvents_congr
    intro l _ hl
    apply realTimeSchedule_congr _ _ _ _ (fuel + 1) _ l (by omega)
    intro m hm
    exact (direct_real_clock_eq_word transition ratesF initial w m (hcert.hA m (by omega)) _).symm
  -- The float public run reads exactly the rounded certificate packets.
  have htape : floatStreamTape ρu ρe (fuel + 1 + c) (fuel + 1 + e) ω =
      floatPacketTapeFrom (fun _ p => [ρu p.2]) (fun _ p => [ρe p.1]) source
        (floatStreamTape ρu ρe c e (streamsDrop (fuel + 1) (fuel + 1) ω)) 0 (fuel + 1) := by
    rw [floatPacketTapeFrom_single, floatStreamTape_split]
    have hsrc : ∀ i : Fin (fuel + 1), source (0 + i.val) = (ω (.inr i), ω (.inl i)) := by
      intro i
      rw [zero_add]
      exact directParse_chronological (fuel + 1) ω i i.isLt
    simp only [hsrc]
  have hinit : initial = states 0 := rfl
  rw [hreal, hreplay, htape, hinit]
  exact float_packet_trajectory_close_from mf mr .direct (by intro h; cases h) htransition states
    (fun l => (extendMarks w l).val) (directFloatClock rates (fun _ p => ρe p.1))
    (fun _ p => [ρu p.2]) (fun _ p => [ρe p.1]) (directRealClock rates) source _ start hf sr hr ε d δ
    fuel cap save
    (direct_float_local_refinement mf states (fun l => (extendMarks w l).val) rates
      (fun l => CF.rates_eq _) (fun _ p => ρe p.1) (fun _ p => ρu p.2) source start fuel cap d η
      hcert.hA hcert.hg hcert.hc)
    (fun l => CF.transition_eq _ _) hcert.hvalid hcert.hstart hcert.hhf hcert.hh hcert.h0 hcert.hd
    hcert.hbudget hcert.hmargin

lemma direct_word_observation_law {σ X : Type} [MeasurableSpace X] {n : ℕ} (model : Model ℝ σ)
    (transition : σ → Fin (n + 1) → σ) (rates : σ → Fin (n + 1) → ℝ) (hr : ∀ x j, 0 ≤ rates x j)
    (initial : σ) (start horizon : ℝ) (fuel : ℕ) (save : Bool)
    (observable : Except Error (TraceObservation ℝ σ) → X) (w : Fin (fuel + 1) → Fin (n + 1))
    (hobs : Measurable (fun ts => observable (holdingSimulationObservation model
      (stateAlongWord transition initial (extendMarks w))
      (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w)
      start horizon fuel save ts))) :
    (iidStreams.restrict (directWordEvent transition rates initial w)).map (fun ω => observable
      (holdingSimulationObservation model (stateAlongWord transition initial (extendMarks w))
        (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w)
        start horizon fuel save (rawWordHoldings (directWordClock transition rates initial w) (fuel + 1)
          (directParse (fuel + 1) ω)))) =
    (targetWordLaw (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks w) l)))
      (extendMarks w) (fuel + 1)).map (fun ts => observable (holdingSimulationObservation model
        (stateAlongWord transition initial (extendMarks w))
        (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w)
        start horizon fuel save ts)) := by
  have hmh : Measurable (rawWordHoldings (directWordClock transition rates initial w) (fuel + 1)) :=
    measurable_rawWordHoldings _ (measurable_directWordClock _ _ _ w) _
  have h1 := Measure.map_map (μ := iidStreams.restrict (directWordEvent transition rates initial w)) hobs
    (hmh.comp (measurable_directParse (fuel + 1)))
  have h2 := Measure.map_map (μ := iidStreams.restrict (directWordEvent transition rates initial w)) hmh
    (measurable_directParse (fuel + 1))
  rw [← h2, directWordEvent_branch, directWord_holding_law _ _ _ hr] at h1
  exact h1.symm

/-- FloatLib Direct simulations on rounded IID streams approximate the exact target
law. `β` is the outer probability that the Direct numerical certificate fails along
the realized reaction word. -/
theorem direct_float_iid_law_bounds {σ ι : Type} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (a b : ℕ) (ha : fuel + 1 ≤ a) (hb : fuel + 1 ≤ b)
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (εobs : ℝ) (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ εobs ∧ If f = I r)
    (hM : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts =>
        let r := holdingSimulationObservation mr states (fun l j => floatReal (ratesF (states l) j))
          marks sr hr fuel save ts
        (T r, I r)))
    (i : ι) (t : ℝ) :
    let Ff := fun ω => observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .direct initial
      start hf (floatStreamTape ρu ρe a b ω) fuel save cap)
    let target := targetSimulationLaw mr transition (fun x j => floatReal (ratesF x j)) initial sr hr fuel
      save (fun r => (T r, I r))
    let β := iidStreams (directFloatGood mf mr htransition transition ratesF lowerF upperF CF initial
      ρu ρe start hf sr hr ε d δ η fuel cap save)ᶜ
    target (jointTail (t + εobs) i) ≤ iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} + β ∧
    iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} ≤ target (jointTail (t - εobs) i) + β := by
  intro Ff target β
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hb
  let rr := fun x j => floatReal (ratesF x j)
  let E := fun w : Fin (fuel + 1) → Fin (n + 1) => directWordEvent transition rr initial w
  let G := fun (w : Fin (fuel + 1) → Fin (n + 1)) (ω : Streams) =>
    let r := holdingSimulationObservation mr (stateAlongWord transition initial (extendMarks w))
      (fun l j => rr (stateAlongWord transition initial (extendMarks w) l) j) (extendMarks w) sr hr fuel
      save (rawWordHoldings (directWordClock transition rr initial w) (fuel + 1) (directParse (fuel + 1) ω))
    (T r, I r)
  have hG : ∀ w, Measurable (G w) := fun w =>
    (hM w).comp ((measurable_rawWordHoldings _ (measurable_directWordClock _ _ _ w) _).comp
      (measurable_directParse (fuel + 1)))
  have htarget : target = Measure.sum (fun w => (iidStreams.restrict (E w)).map (G w)) := by
    simp only [target, targetSimulationLaw]
    congr 1
    funext w
    exact (direct_word_observation_law mr transition rr CR.nonnegative initial sr hr fuel save
      (fun r => (T r, I r)) w (hM w)).symm
  apply word_coupling_tail_bounds E (fun w => measurableSet_directWordEvent _ _ _ w)
    (directWordEvent_disjoint _ _ _ (fuel + 1)) (directWordEvent_total _ _ _ CR.nonnegative (fuel + 1))
    G hG target htarget Ff Tf If _ εobs
  intro w ω ⟨hEw, hgood⟩
  obtain ⟨w', hE', hreal, hclose⟩ := direct_float_iid_close mf mr htransition transition ratesF lowerF
    upperF CF CR initial ρu ρe start hf sr hr ε d δ η hsr fuel cap save c e ω hgood
  have hw : w' = w := by
    by_contra hne
    exact (Set.disjoint_left.mp (directWordEvent_disjoint transition rr initial (fuel + 1) hne)) hE' hEw
  subst hw
  have h := hobs _ _ hclose
  rw [hreal] at h
  exact h

/-! ### Float tapes of sequential readers -/

/-- Readers whose float packet tape is the rounded block of stream draws they consumed. -/
structure FloatTapeCompatible {γ : Type} [MeasurableSpace γ] (u e : Nat → γ → List Binary64)
    (r : ℕ → StreamReader γ) (ρu ρe : ℝ → Binary64) : Prop where
  uniforms : ∀ l ω, u l ((r l).read ω) =
    (List.range ((r l).usedU ω)).map (fun i => ρu (ω (.inl i)))
  exponentials : ∀ l ω, e l ((r l).read ω) =
    (List.range ((r l).usedV ω)).map (fun i => ρe (ω (.inr i)))

lemma floatPacketTapeFrom_readers {γ : Type} [MeasurableSpace γ] (u e : Nat → γ → List Binary64)
    (r : ℕ → StreamReader γ) (ρu ρe : ℝ → Binary64) (hc : FloatTapeCompatible u e r ρu ρe)
    (K : ℕ) (ω : Streams) (fallback : γ) (tail : Tape Binary64) :
    ∀ c k, k + c ≤ K →
      floatPacketTapeFrom u e (rawChronological fallback (readerParse r K ω).1) tail k c =
        ⟨(List.range ((readerOffsets r (k + c) ω).1 - (readerOffsets r k ω).1)).map
            (fun i => ρu (ω (.inl ((readerOffsets r k ω).1 + i)))) ++ tail.uniforms,
          (List.range ((readerOffsets r (k + c) ω).2 - (readerOffsets r k ω).2)).map
            (fun i => ρe (ω (.inr ((readerOffsets r k ω).2 + i)))) ++ tail.exponentials⟩ := by
  intro c
  induction c with
  | zero => intro k _; simp [floatPacketTapeFrom]
  | succ c ih =>
    intro k hk
    have hsrc : rawChronological fallback (readerParse r K ω).1 k =
        (r k).read (streamsDrop (readerOffsets r k ω).1 (readerOffsets r k ω).2 ω) := by
      simp only [rawChronological, show k < K by omega, dite_true]
      rw [readerParse_chron r K ω k (by omega), readerParse_rest_offsets]
    have hnext := ih (k + 1) (by omega)
    have hmono := readerOffsets_mono r (k + 1) c ω
    have hk1 : readerOffsets r (k + 1) ω =
        ((readerOffsets r k ω).1 + (r k).usedU (streamsDrop (readerOffsets r k ω).1
            (readerOffsets r k ω).2 ω),
          (readerOffsets r k ω).2 + (r k).usedV (streamsDrop (readerOffsets r k ω).1
            (readerOffsets r k ω).2 ω)) := by
      simp only [readerOffsets, readerParse_rest_offsets]
    rw [floatPacketTapeFrom, hnext, hsrc, hc.uniforms, hc.exponentials]
    rw [show k + (c + 1) = k + 1 + c by omega]
    simp only [hk1] at hmono ⊢
    apply Tape.mk.injEq _ _ _ _ |>.mpr
    constructor
    · rw [← List.append_assoc]
      congr 1
      rw [show (readerOffsets r (k + 1 + c) ω).1 - (readerOffsets r k ω).1 =
          (r k).usedU (streamsDrop (readerOffsets r k ω).1 (readerOffsets r k ω).2 ω) +
            ((readerOffsets r (k + 1 + c) ω).1 - ((readerOffsets r k ω).1 +
              (r k).usedU (streamsDrop (readerOffsets r k ω).1 (readerOffsets r k ω).2 ω))) by omega,
        List.range_add, List.map_append, List.map_map]
      simp [streamsDrop, Nat.add_assoc, Function.comp_def]
    · rw [← List.append_assoc]
      congr 1
      rw [show (readerOffsets r (k + 1 + c) ω).2 - (readerOffsets r k ω).2 =
          (r k).usedV (streamsDrop (readerOffsets r k ω).1 (readerOffsets r k ω).2 ω) +
            ((readerOffsets r (k + 1 + c) ω).2 - ((readerOffsets r k ω).2 +
              (r k).usedV (streamsDrop (readerOffsets r k ω).1 (readerOffsets r k ω).2 ω))) by omega,
        List.range_add, List.map_append, List.map_map]
      simp [streamsDrop, Nat.add_assoc, Function.comp_def]

lemma flatMap_float_pairs : ∀ (m : ℕ) (f : ℕ → Binary64),
    (List.ofFn (fun j : Fin m => (f (2 * j), f (2 * j + 1)))).flatMap
      (fun p : Binary64 × Binary64 => [p.1, p.2]) = (List.range (2 * m)).map f
  | 0, _ => by simp
  | m + 1, f => by
    rw [List.ofFn_succ, List.flatMap_cons]
    have ih := flatMap_float_pairs m (fun i => f (2 + i))
    have hpairs : (fun j : Fin m => (f (2 * (j.succ : ℕ)), f (2 * (j.succ : ℕ) + 1))) =
        (fun j : Fin m => (f (2 + 2 * (j : ℕ)), f (2 + (2 * (j : ℕ) + 1)))) := by
      funext j
      simp only [Fin.val_succ]
      congr 2 <;> omega
    rw [hpairs, ih, show 2 * (m + 1) = 2 + 2 * m by ring, List.range_add, List.map_append,
      List.map_map]
    simp [List.range_succ, Function.comp_def]

/-! ### RSSA -/

/-- Rounded proposal draws of a first-success packet. -/
noncomputable def rssaFloatExp {n : ℕ} (ρe : ℝ → Binary64) (_k : ℕ) (p : RSSAStoppingInput n) :
    Fin (p.1.1 + 1) → Binary64 := fun j => ρe (p.2.1 j)

noncomputable def rssaFloatSel {n : ℕ} (ρu : ℝ → Binary64) (_k : ℕ) (p : RSSAStoppingInput n) :
    Fin (p.1.1 + 1) → Binary64 := fun j => ρu (p.2.2 j).1

noncomputable def rssaFloatAcc {n : ℕ} (ρu : ℝ → Binary64) (_k : ℕ) (p : RSSAStoppingInput n) :
    Fin (p.1.1 + 1) → Binary64 := fun j => ρu (p.2.2 j).2

section RSSAFloat

variable {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
  (htransition : ∀ x i, mf.transition x i = mr.transition x i)
  (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
  (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
  (hbv : ∀ x j, 0 ≤ floatReal (lowerF x j) ∧ floatReal (lowerF x j) ≤ floatReal (ratesF x j) ∧
    floatReal (ratesF x j) ≤ floatReal (upperF x j))
  (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ) (fuel cap : ℕ)
  (save : Bool)

/-- Numerical certificate event of the coupled capped RSSA simulations. -/
noncomputable def rssaFloatGood : Set Streams :=
  {ω | (∀ x, ω x ∈ Ioo (0 : ℝ) 1) ∧ ∃ w : Fin (fuel + 1) → Fin (n + 1),
    (∀ l, l < fuel + 1 →
      (readerParse (rssaWordReaders transition (fun x j => floatReal (ratesF x j))
        (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)) hbv initial w) l ω).2 ∈
        (rssaWordReaders transition (fun x j => floatReal (ratesF x j))
          (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)) hbv initial w l).good) ∧
    ω ∈ rssaWordEvent transition (fun x j => floatReal (ratesF x j)) (fun x j => floatReal (lowerF x j))
      (fun x j => floatReal (upperF x j)) hbv initial w ∧
    ω ∈ rssaWordCapEvent transition (fun x j => floatReal (ratesF x j)) (fun x j => floatReal (lowerF x j))
      (fun x j => floatReal (upperF x j)) hbv initial w cap ∧
    RSSATrajectoryConditions mf mr htransition (stateAlongWord transition initial (extendMarks w))
      (fun l => (extendMarks w l).val)
      (fun l => Array.ofFn (ratesF (stateAlongWord transition initial (extendMarks w) l)))
      (fun l => ⟨Array.ofFn (lowerF (stateAlongWord transition initial (extendMarks w) l)),
        Array.ofFn (upperF (stateAlongWord transition initial (extendMarks w) l))⟩)
      (fun l => CF.rates_eq _) (fun l => CF.bounds_eq _) (fun l => CF.transition_eq _ _)
      (rssaFloatExp ρe) (rssaFloatSel ρu) (rssaFloatAcc ρu)
      (rawChronological ⟨(0, 0), (fun _ => 1 / 2, fun _ => (1 / 2, 1 / 2))⟩
        (rssaWordParse transition (fun x j => floatReal (ratesF x j)) (fun x j => floatReal (lowerF x j))
          (fun x j => floatReal (upperF x j)) hbv initial w ω))
      start hf sr hr ε d δ η fuel cap save}

end RSSAFloat

lemma rssaWord_floatTapeCompatible {σ : Type} {n : ℕ} (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (hb : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j) (initial : σ)
    {K : ℕ} (w : Fin K → Fin (n + 1)) (ρu ρe : ℝ → Binary64) :
    FloatTapeCompatible (fun k p => proposalFloatUniforms (rssaFloatSel (n := n + 1) ρu k p)
      (rssaFloatAcc ρu k p)) (fun k p => List.ofFn (rssaFloatExp (n := n + 1) ρe k p))
      (rssaWordReaders transition rates lower upper hb initial w) ρu ρe where
  uniforms := by
    intro l ω
    simp only [rssaWordReaders, rssaStateReader, rssaReader, proposalBlock, proposalFloatUniforms,
      rssaFloatSel, rssaFloatAcc]
    exact flatMap_float_pairs _ (fun i => ρu (ω (.inl i)))
  exponentials := by
    intro l ω
    simp only [rssaWordReaders, rssaStateReader, rssaReader, proposalBlock, rssaFloatExp]
    exact ofFn_eq_range_map _ (fun i => ρe (ω (.inr i)))

lemma rssa_active_total {n : ℕ} (rates : Fin (n + 1) → Binary64)
    (hfin : ∀ j, ExecFloat.Binary.isFinite (rates j) = true)
    (hn : ∀ j, 0 ≤ floatReal (rates j))
    (ha : (Array.ofFn rates).any (binary64Arithmetic.lt binary64Arithmetic.zero) = true) :
    0 < ∑ j, floatReal (rates j) := by
  obtain ⟨j, hj, hp⟩ := Array.any_eq_true.mp ha
  have hpos : 0 < floatReal (rates ⟨j, by simpa using hj⟩) := by
    have hp' : binary64Arithmetic.lt 0 (rates ⟨j, by simpa using hj⟩) = true := by
      have h0 : binary64Arithmetic.zero = (0 : Binary64) := rfl
      simpa [Array.getElem_ofFn, h0] using hp
    exact real_positive_of_flag _ (hfin _) hp'
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ _))

/-- An accepted proposal certifies a positive rate on the accepted channel. -/
lemma proposalBranch_total_pos {n : ℕ} (rates lower upper : Fin (n + 1) → ℝ)
    (hb : ∀ j, 0 ≤ lower j ∧ lower j ≤ rates j ∧ rates j ≤ upper j) (k i : ℕ)
    (v : Fin (k + 1) → ℝ × ℝ) (hv : v ∈ proposalBranch (List.ofFn rates) (List.ofFn lower)
      (List.ofFn upper) k i) : 0 < ∑ j, rates j := by
  have hk := (mem_univ_pi.mp hv) (Fin.last k)
  simp only [Fin.val_last, lt_irrefl, ite_false, mem_preimage, mem_singleton_iff] at hk
  have hi : i < n + 1 := by
    have := proposalMark_some_bound _ _ _ _ i hk
    simpa using this
  have hacc := ((proposalMark_some_iff _ _ _ _ i).mp hk).2
  have hget : ∀ f : Fin (n + 1) → ℝ, (List.ofFn f)[i]! = f ⟨i, hi⟩ := by
    intro f
    have hlen : i < (List.ofFn f).length := by simpa using hi
    rw [getElem!_pos (List.ofFn f) i hlen, List.getElem_ofFn]
  rw [hget, hget] at hacc
  have hpos : 0 < rates ⟨i, hi⟩ := by
    simp only [rssaAccept, realArithmetic, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hacc
    rcases hacc with ⟨hl, _⟩ | ⟨hr, _⟩
    · exact lt_of_lt_of_le hl (hb _).2.1
    · exact hr
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun j _ => (hb j).1.trans (hb j).2.1)
    (Finset.mem_univ _))

/-- On the RSSA certificate event, the public FloatLib capped RSSA simulator is
trace-close to the public real capped RSSA simulator on the same IID streams. -/
theorem rssa_float_iid_close {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (a b : ℕ)
    (ha : 2 * cap * (fuel + 1) ≤ a) (hb : cap * (fuel + 1) ≤ b) (ω : Streams)
    (hω : ω ∈ rssaFloatGood mf mr htransition transition ratesF lowerF upperF CF CR.bounds_valid
      initial ρu ρe start hf sr hr ε d δ η fuel cap save) :
    ∃ w : Fin (fuel + 1) → Fin (n + 1),
      ω ∈ rssaWordEvent transition (fun x j => floatReal (ratesF x j)) (fun x j => floatReal (lowerF x j))
        (fun x j => floatReal (upperF x j)) CR.bounds_valid initial w ∧
      observeRun (simulate realArithmetic (tapeSource ℝ) mr .rssa initial sr hr (streamTape a b ω)
        fuel save cap) =
        holdingSimulationObservation mr (stateAlongWord transition initial (extendMarks w))
          (fun l j => floatReal (ratesF (stateAlongWord transition initial (extendMarks w) l) j))
          (extendMarks w) sr hr fuel save
          (rawWordHoldings (fun l => rssaStoppingTime (n := n + 1) (List.ofFn (completedUpper
            (fun j => floatReal (ratesF (stateAlongWord transition initial (extendMarks w) l) j))
            (fun j => floatReal (upperF (stateAlongWord transition initial (extendMarks w) l) j)))))
            (fuel + 1) (rssaWordParse transition (fun x j => floatReal (ratesF x j))
              (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)) CR.bounds_valid
              initial w ω)) ∧
      TraceClose δ
        (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .rssa initial start hf
          (floatStreamTape ρu ρe a b ω) fuel save cap))
        (observeRun (simulate realArithmetic (tapeSource ℝ) mr .rssa initial sr hr (streamTape a b ω)
          fuel save cap)) := by
  obtain ⟨hcoord, w, hgoodR, hE, hcap, hcert⟩ := hω
  let rr := fun x j => floatReal (ratesF x j)
  let lr := fun x j => floatReal (lowerF x j)
  let ur := fun x j => floatReal (upperF x j)
  let states := stateAlongWord transition initial (extendMarks w)
  let rates := fun l => Array.ofFn (ratesF (states l))
  let bounds : Nat → RateBounds Binary64 := fun l =>
    ⟨Array.ofFn (lowerF (states l)), Array.ofFn (upperF (states l))⟩
  let r := rssaWordReaders transition rr lr ur CR.bounds_valid initial w
  let parse := rssaWordParse transition rr lr ur CR.bounds_valid initial w ω
  let fallback : RSSAStoppingInput (n + 1) := ⟨(0, 0), (fun _ => 1 / 2, fun _ => (1 / 2, 1 / 2))⟩
  let source := rawChronological fallback parse
  have hreal := rssa_capped_driver_executes mr transition rr lr ur CR initial sr hr hsr fuel cap save a b
    ha hb w ω hcoord hgoodR hE hcap
  refine ⟨w, hE, hreal, ?_⟩
  -- Every step of the certified schedule has a positive real total rate.
  have hA : ∀ l, l ≤ fuel → 0 < ∑ j, rr (states l) j := by
    intro l hl
    have hg := (hcert.hg l hl).2.2.2
    simp only [rates, bounds, Array.toList_ofFn, List.map_ofFn] at hg
    exact proposalBranch_total_pos (fun j => rr (states l) j) (fun j => lr (states l) j)
      (fun j => ur (states l) j) (fun j => CR.bounds_valid _ j) _ _ _ hg
  have hclock : ∀ l, l ≤ fuel → ∀ p, rssaStoppingTime (n := n + 1)
      (List.ofFn (completedUpper (fun j => rr (states l) j) (fun j => ur (states l) j))) p =
      rssaRealClock bounds l p := by
    intro l hl p
    simp only [rssaRealClock, bounds, completedUpper, hA l hl, ite_true, Array.toList_ofFn,
      List.map_ofFn]
    rfl
  have hreplay : holdingSimulationObservation mr states (fun l j => rr (states l) j) (extendMarks w) sr hr
      fuel save (rawWordHoldings (fun l => rssaStoppingTime (n := n + 1) (List.ofFn (completedUpper
        (fun j => rr (states l) j) (fun j => ur (states l) j)))) (fuel + 1) parse) =
      replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (rssaRealClock bounds) source sr)
          (fun l => (extendMarks w l).val) 0 (fuel + 1)) := by
    rw [← packet_real_replay_eq_holdings mr states (fun l j => rr (states l) j) (extendMarks w) _
      fallback sr hr fuel save hA]
    unfold packetRealReplay
    congr 1
    apply scheduledEvents_congr
    intro l _ hl
    apply realTimeSchedule_congr _ _ _ _ (fuel + 1) _ l (by omega)
    intro m hm
    exact hclock m (by omega) _
  -- The float public run reads exactly the rounded first-success blocks.
  have hoff := rssaWord_offsets_bound transition rr lr ur CR.bounds_valid initial w cap ω hcap (fuel + 1)
    le_rfl
  set OU := (readerOffsets r (fuel + 1) ω).1 with hOU
  set OV := (readerOffsets r (fuel + 1) ω).2 with hOV
  have hOUa : OU ≤ a := hoff.1.trans ha
  have hOVb : OV ≤ b := hoff.2.trans hb
  let tail : Tape Binary64 := ⟨(List.range (a - OU)).map (fun i => ρu (ω (.inl (OU + i)))),
    (List.range (b - OV)).map (fun i => ρe (ω (.inr (OV + i))))⟩
  have htape : floatStreamTape ρu ρe a b ω =
      floatPacketTapeFrom (fun k p => proposalFloatUniforms (rssaFloatSel (n := n + 1) ρu k p)
        (rssaFloatAcc ρu k p)) (fun k p => List.ofFn (rssaFloatExp (n := n + 1) ρe k p)) source tail 0
        (fuel + 1) := by
    show floatStreamTape ρu ρe a b ω = floatPacketTapeFrom _ _
      (rawChronological fallback (readerParse r (fuel + 1) ω).1) tail 0 (fuel + 1)
    rw [floatPacketTapeFrom_readers _ _ r ρu ρe (rssaWord_floatTapeCompatible transition rr lr ur
      CR.bounds_valid initial w ρu ρe) (fuel + 1) ω fallback tail (fuel + 1) 0 (by omega)]
    have h0 : readerOffsets r 0 ω = (0, 0) := rfl
    simp only [h0, Nat.sub_zero, zero_add]
    rw [← hOU, ← hOV]
    simp only [floatStreamTape, tail]
    rw [ofFn_eq_range_map a (fun i => ρu (ω (.inl i))), ofFn_eq_range_map b (fun i => ρe (ω (.inr i)))]
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hOUa
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hOVb
    rw [hc, he, List.range_add, List.range_add, List.map_append, List.map_append, List.map_map,
      List.map_map, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    rfl
  have hinit : initial = states 0 := rfl
  have hupper : ∀ k, k ≤ fuel → ∀ x ∈ (bounds k).upper.toList.map floatReal, 0 ≤ x := by
    intro k _ x hx
    simp only [bounds, Array.toList_ofFn, List.map_ofFn, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact ((CR.bounds_valid _ j).1.trans (CR.bounds_valid _ j).2.1).trans (CR.bounds_valid _ j).2.2
  have hrun : observeRun (simulate realArithmetic (tapeSource ℝ) mr .rssa initial sr hr (streamTape a b ω)
      fuel save cap) = replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (rssaRealClock bounds) source sr)
          (fun l => (extendMarks w l).val) 0 (fuel + 1)) := hreal.trans hreplay
  rw [hrun, htape, hinit]
  exact float_packet_trajectory_close_from mf mr .rssa (by intro h; cases h) htransition states
    (fun l => (extendMarks w l).val) (rssaFloatClock bounds (rssaFloatExp ρe))
    (fun k p => proposalFloatUniforms (rssaFloatSel ρu k p) (rssaFloatAcc ρu k p))
    (fun k p => List.ofFn (rssaFloatExp ρe k p)) (rssaRealClock bounds) source tail start hf sr hr ε d δ
    fuel cap save
    (rssa_float_local_refinement mf states (fun l => (extendMarks w l).val) rates bounds
      (fun l => CF.rates_eq _) (fun l => CF.bounds_eq _) (rssaFloatExp ρe) (rssaFloatSel ρu)
      (rssaFloatAcc ρu) source start fuel cap d η hupper hcert.hB hcert.hg hcert.hc)
    (fun l => CF.transition_eq _ _) hcert.hvalid hcert.hstart hcert.hhf hcert.hh hcert.h0 hcert.hd
    hcert.hbudget hcert.hmargin

lemma rssa_word_observation_law {σ X : Type} [MeasurableSpace X] {n : ℕ} (model : Model ℝ σ)
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → ℝ)
    (hb : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j)
    (initial : σ) (start horizon : ℝ) (fuel : ℕ) (save : Bool)
    (observable : Except Error (TraceObservation ℝ σ) → X) (w : Fin (fuel + 1) → Fin (n + 1))
    (hobs : Measurable (fun ts => observable (holdingSimulationObservation model
      (stateAlongWord transition initial (extendMarks w))
      (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w)
      start horizon fuel save ts))) :
    (iidStreams.restrict (rssaWordEvent transition rates lower upper hb initial w)).map (fun ω => observable
      (holdingSimulationObservation model (stateAlongWord transition initial (extendMarks w))
        (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w)
        start horizon fuel save (rawWordHoldings (fun l => rssaStoppingTime (n := n + 1) (List.ofFn
          (completedUpper (rates (stateAlongWord transition initial (extendMarks w) l))
            (upper (stateAlongWord transition initial (extendMarks w) l))))) (fuel + 1)
          (rssaWordParse transition rates lower upper hb initial w ω)))) =
    (targetWordLaw (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks w) l)))
      (extendMarks w) (fuel + 1)).map (fun ts => observable (holdingSimulationObservation model
        (stateAlongWord transition initial (extendMarks w))
        (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w)
        start horizon fuel save ts)) := by
  have hmh : Measurable (rawWordHoldings (fun l => rssaStoppingTime (n := n + 1) (List.ofFn
      (completedUpper (rates (stateAlongWord transition initial (extendMarks w) l))
        (upper (stateAlongWord transition initial (extendMarks w) l))))) (fuel + 1)) :=
    measurable_rawWordHoldings _ (fun l => measurable_rssaStoppingTime _) _
  have hparse := measurable_rssaWordParse transition rates lower upper hb initial w
  have h1 := Measure.map_map (μ := iidStreams.restrict (rssaWordEvent transition rates lower upper hb
    initial w)) hobs (hmh.comp hparse)
  have h2 := Measure.map_map (μ := iidStreams.restrict (rssaWordEvent transition rates lower upper hb
    initial w)) hmh hparse
  rw [← h2, rssaWordEvent_branch transition rates lower upper hb initial w,
    rssaWord_holding_law transition rates lower upper hb initial w] at h1
  exact h1.symm

/-- FloatLib capped RSSA simulations on rounded IID streams approximate the exact
target law. `β` is the outer probability that the realized first-success blocks
exceed the cap or violate the RSSA numerical certificate. -/
theorem rssa_float_iid_law_bounds {σ ι : Type} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (a b : ℕ)
    (ha : 2 * cap * (fuel + 1) ≤ a) (hb : cap * (fuel + 1) ≤ b)
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (εobs : ℝ) (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ εobs ∧ If f = I r)
    (hM : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts =>
        let r := holdingSimulationObservation mr states (fun l j => floatReal (ratesF (states l) j))
          marks sr hr fuel save ts
        (T r, I r)))
    (i : ι) (t : ℝ) :
    let Ff := fun ω => observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .rssa initial
      start hf (floatStreamTape ρu ρe a b ω) fuel save cap)
    let target := targetSimulationLaw mr transition (fun x j => floatReal (ratesF x j)) initial sr hr fuel
      save (fun r => (T r, I r))
    let β := iidStreams (rssaFloatGood mf mr htransition transition ratesF lowerF upperF CF
      CR.bounds_valid initial ρu ρe start hf sr hr ε d δ η fuel cap save)ᶜ
    target (jointTail (t + εobs) i) ≤ iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} + β ∧
    iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} ≤ target (jointTail (t - εobs) i) + β := by
  intro Ff target β
  let rr := fun x j => floatReal (ratesF x j)
  let lr := fun x j => floatReal (lowerF x j)
  let ur := fun x j => floatReal (upperF x j)
  let E := fun w : Fin (fuel + 1) → Fin (n + 1) => rssaWordEvent transition rr lr ur CR.bounds_valid initial w
  let G := fun (w : Fin (fuel + 1) → Fin (n + 1)) (ω : Streams) =>
    let r := holdingSimulationObservation mr (stateAlongWord transition initial (extendMarks w))
      (fun l j => rr (stateAlongWord transition initial (extendMarks w) l) j) (extendMarks w) sr hr fuel
      save (rawWordHoldings (fun l => rssaStoppingTime (n := n + 1) (List.ofFn
        (completedUpper (rr (stateAlongWord transition initial (extendMarks w) l))
          (ur (stateAlongWord transition initial (extendMarks w) l))))) (fuel + 1)
        (rssaWordParse transition rr lr ur CR.bounds_valid initial w ω))
    (T r, I r)
  have hG : ∀ w, Measurable (G w) := fun w =>
    (hM w).comp ((measurable_rawWordHoldings _ (fun l => measurable_rssaStoppingTime _) _).comp
      (measurable_rssaWordParse transition rr lr ur CR.bounds_valid initial w))
  have htarget : target = Measure.sum (fun w => (iidStreams.restrict (E w)).map (G w)) := by
    simp only [target, targetSimulationLaw]
    congr 1
    funext w
    exact (rssa_word_observation_law mr transition rr lr ur CR.bounds_valid initial sr hr fuel save
      (fun r => (T r, I r)) w (hM w)).symm
  have hnn : ∀ x j, 0 ≤ rr x j := fun x j => CR.nonnegative x j
  apply word_coupling_tail_bounds E (fun w => measurableSet_rssaWordEvent _ _ _ _ _ _ w)
    (rssaWordEvent_disjoint _ _ _ _ _ _ (fuel + 1))
    (rssaWordEvent_total _ _ _ _ CR.bounds_valid _ (fuel + 1) hnn) G hG target htarget Ff Tf If _ εobs
  intro w ω ⟨hEw, hgood⟩
  obtain ⟨w', hE', hreal, hclose⟩ := rssa_float_iid_close mf mr htransition transition ratesF lowerF
    upperF CF CR initial ρu ρe start hf sr hr ε d δ η hsr fuel cap save a b ha hb ω hgood
  have hw : w' = w := by
    by_contra hne
    exact (Set.disjoint_left.mp (rssaWordEvent_disjoint transition rr lr ur CR.bounds_valid initial
      (fuel + 1) hne)) hE' hEw
  subst hw
  have h := hobs _ _ hclose
  rw [hreal] at h
  exact h

/-! ### NRM -/

/-- Complete FloatLib NRM trajectory approximation, with any unread tape suffix. -/
theorem nrm_float_trajectory_close_from {σ : Type} {n : Nat} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Fin (n + 1))
    (rates e : Nat → Fin (n + 1) → Binary64) (er : Nat → Fin (n + 1) → ℝ)
    (hm : ∀ k, mf.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, mf.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ) (fuel cap : Nat) (save : Bool)
    (us es : List Binary64)
    (hp : ∀ l j, binary64Arithmetic.lt 0 (rates l j) = true)
    (hv : ∀ l j, validRate binary64Arithmetic (rates l j) = true)
    (hi : NRMInitConditions (rates 0) (e 0) (er 0) start sr (η 0))
    (hc : ∀ k, k < fuel → NRMUpdateConditions (rates k) (rates (k + 1))
      (nrmFloatClocks rates e marks start k) (e (k + 1)) (er (k + 1))
      (nrmFloatTimes rates e marks start (k + 1)) (η k) (η k) (η (k + 1)) (marks k))
    (hcacheFinite : ∀ k, k ≤ fuel → ∀ j, ExecFloat.Binary.isFinite (nrmFloatClocks rates e marks start k j) = true)
    (hgap : ∀ k, k ≤ fuel → ∀ j, j ≠ marks k →
      nrmRealClocks rates er marks sr k (marks k) + 2 * η k < nrmRealClocks rates er marks sr k j)
    (hinc : ∀ k, k ≤ fuel → binary64Arithmetic.le (nrmFloatTimes rates e marks start k)
      (nrmFloatTimes rates e marks start (k + 1)) = true)
    (hrinc : ∀ k, k ≤ fuel → nrmRealTimes rates er marks sr k ≤ nrmRealTimes rates er marks sr (k + 1))
    (hbudget : ∀ k, k ≤ fuel → η k ≤ δ)
    (hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true) (hstart : binary64Arithmetic.lt start hf = true)
    (hhf : ExecFloat.Binary.isFinite hf = true) (hh : |floatReal hf - hr| ≤ δ)
    (h0 : |floatReal start - sr| ≤ δ)
    (hmargin : ∀ k, k ≤ fuel → 2 * δ < |nrmRealTimes rates er marks sr (k + 1) - hr|) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .nrm (states 0) start hf
        ⟨us, List.ofFn (e 0) ++ (nrmFloatTape rates e marks 0 fuel ++ es)⟩ fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (nrmRealTimes rates er marks sr) (fun k => (marks k).val) 0 (fuel + 1))) := by
  let tf := nrmFloatTimes rates e marks start
  let tr := nrmRealTimes rates er marks sr
  let tape := fun k count => (⟨us, nrmFloatTape rates e marks k (count - 1) ++ es⟩ : Tape Binary64)
  let cache := fun k => some (nrmFloatCache rates e marks start k)
  have herr := nrm_float_cache_errors rates e er marks start sr η fuel hp hv hi hc
  have hnext k hk := nrm_float_winner_approx (rates k) (nrmFloatClocks rates e marks start k)
    (nrmRealClocks rates er marks sr k) (marks k) (η k) (hcacheFinite k hk) (herr k hk) (hgap k hk)
  apply simulate_float_schedule_close (tapeSource Binary64) mf mr .nrm htransition states tf tr
    (fun k => (marks k).val) hf hr δ fuel cap save tape (fun k count => tape k (count + 1)) cache
    (⟨us, List.ofFn (e 0) ++ (nrmFloatTape rates e marks 0 fuel ++ es)⟩ : Tape Binary64)
  · dsimp only [initializeCache]
    dsimp only [tf, nrmFloatTimes]
    rw [hm 0, (nrm_float_initialize_conditions _ _ _ _ _ _ hi us (nrmFloatTape rates e marks 0 fuel ++ es)).1]
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, tape, cache, tf,
      nrmFloatTimes, nrmFloatCache, nrmFloatClocks, Nat.add_sub_cancel]
  · exact hvalid
  · exact hstart
  · exact hhf
  · exact hh
  · exact h0
  · intro k count hk
    dsimp only [sampleEvent, cache, nrmFloatCache]
    rw [(hnext k (by omega)).1]
    rfl
  · exact hs
  · intro k count hk
    dsimp only [refreshCache, cache]
    rw [hm (k + 1)]
    simp only [Array.size_ofFn]
    have hh := nrm_float_update_schedule rates e marks start k hp hv (hcacheFinite k (by omega) (marks k))
      (hc k (by omega)).flags us (nrmFloatTape rates e marks (k + 1) count ++ es)
    change (do
      let result ← nrmUpdate binary64Arithmetic (tapeSource Binary64) (nrmFloatCache rates e marks start k)
        (Array.ofFn (rates (k + 1))) (marks k).val (tf (k + 1)) (List.range (n + 1)).toArray
        ⟨us, nrmFloatTape rates e marks k (count + 1) ++ es⟩
      pure (some result.1, result.2)) = _
    rw [nrmFloatTape, List.append_assoc, hh]
    rfl
  · intro k hk
    exact hcacheFinite k hk (marks k)
  · exact hinc
  · exact hrinc
  · intro k hk
    exact (herr k hk (marks k)).trans (hbudget k hk)
  · exact hmargin

/-- Primitive values selected by a fresh-clock pattern, in channel order. -/
noncomputable def selectedValues {m : ℕ} (f : Fin m → Bool) (u : Fin m → ℝ) : List ℝ :=
  (List.ofFn (fun j => if f j then some (u j) else none)).filterMap id

lemma selectedValues_succ {m : ℕ} (f : Fin (m + 1) → Bool) (u : Fin (m + 1) → ℝ) :
    selectedValues f u = (if f 0 then [u 0] else []) ++
      selectedValues (fun j => f j.succ) (fun j => u j.succ) := by
  unfold selectedValues
  rw [List.ofFn_succ]
  cases h : f 0 <;> simp [h]

/-- The selected values of a stream row are consecutive exponential-source draws. -/
lemma selectedValues_row : ∀ (m : ℕ) (f : Fin m → Bool) (a b : ℕ) (ω : Streams),
    selectedValues f (fun j => ω (nrmRowIndex m f a b j)) =
      (List.range (freshCount m f)).map (fun r => ω (.inr (b + r)))
  | 0, _, _, _, _ => by simp [selectedValues, freshCount]
  | m + 1, f, a, b, ω => by
    rw [selectedValues_succ]
    have htail := selectedValues_row m (fun j => f j.succ) (a + 1) (if f 0 then b + 1 else b) ω
    have hu : (fun j : Fin m => ω (nrmRowIndex (m + 1) f a b j.succ)) =
        (fun j => ω (nrmRowIndex m (fun j => f j.succ) (a + 1) (if f 0 then b + 1 else b) j)) := by
      funext j
      simp [nrmRowIndex]
    rw [hu, htail]
    by_cases h0 : f 0 = true
    · simp only [h0, ite_true, freshCount]
      rw [Nat.add_comm 1, List.range_succ_eq_map]
      simp [nrmRowIndex, h0, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
    · simp only [h0, Bool.false_eq_true, ite_false, List.nil_append, freshCount, zero_add]

lemma freshPattern_tail {m : ℕ} (old new : Fin (m + 1) → ℝ) (index fired : ℕ) :
    (fun j : Fin m => freshPattern old new index fired j.succ) =
      freshPattern (fun j => old j.succ) (fun j => new j.succ) (index + 1) fired := by
  funext j
  simp [freshPattern, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

lemma nrmFreshExponentials_selected : ∀ {m : ℕ} (old new u : Fin m → ℝ) (index fired : ℕ),
    nrmFreshExponentials old new u index fired =
      (selectedValues (freshPattern old new index fired) u).map (fun x => -log x)
  | 0, _, _, _, _, _ => by simp [nrmFreshExponentials, selectedValues]
  | m + 1, old, new, u, index, fired => by
    rw [nrmFreshExponentials_succ, selectedValues_succ, freshPattern_tail,
      nrmFreshExponentials_selected (fun j => old j.succ) (fun j => new j.succ) (fun j => u j.succ)
        (index + 1) fired, List.map_append]
    congr 1
    simp only [freshPattern, Fin.val_zero, add_zero]
    cases nrmFresh (old 0) (new 0) index fired <;> simp

lemma updateTape_succ {m : ℕ} (old new e : Fin (m + 1) → Binary64) (index fired : ℕ) :
    updateTape binary64Arithmetic old new e index fired =
      (if updateFresh binary64Arithmetic (old 0) (new 0) index fired then [e 0] else []) ++
        updateTape binary64Arithmetic (fun j => old j.succ) (fun j => new j.succ) (fun j => e j.succ)
          (index + 1) fired := by
  unfold updateTape
  rw [List.ofFn_succ]
  cases h : updateFresh binary64Arithmetic (old 0) (new 0) index fired <;>
    simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma updateTape_selected : ∀ {m : ℕ} (oldF newF : Fin m → Binary64) (u : Fin m → ℝ)
    (ρe : ℝ → Binary64) (index fired : ℕ),
    (∀ j, ExecFloat.Binary.isFinite (oldF j) = true ∧ ExecFloat.Binary.isFinite (newF j) = true) →
    updateTape binary64Arithmetic oldF newF (fun j => ρe (u j)) index fired =
      (selectedValues (freshPattern (fun j => floatReal (oldF j)) (fun j => floatReal (newF j)) index fired)
        u).map ρe
  | 0, _, _, _, _, _, _, _ => by simp [updateTape, selectedValues]
  | m + 1, oldF, newF, u, ρe, index, fired, hfin => by
    have hpos : ∀ x : Binary64, ExecFloat.Binary.isFinite x = true →
        binary64Arithmetic.lt binary64Arithmetic.zero x = decide (0 < floatReal x) := by
      intro x hx
      change decide ((0 : Binary64) < x) = decide (0 < floatReal x)
      have h := float_lt_real 0 x float_zero_finite hx
      rw [floatReal_zero] at h
      exact decide_eq_decide.mpr h
    have hfresh : updateFresh binary64Arithmetic (oldF 0) (newF 0) index fired =
        nrmFresh (floatReal (oldF 0)) (floatReal (newF 0)) index fired := by
      simp only [updateFresh, nrmFresh, hpos _ (hfin 0).1, hpos _ (hfin 0).2]
      by_cases hn : 0 < floatReal (newF 0) <;> by_cases ho : 0 < floatReal (oldF 0) <;>
        by_cases hf : index = fired <;> simp [hn, ho, hf]
    rw [updateTape_succ, selectedValues_succ, freshPattern_tail]
    have ih := updateTape_selected (fun j => oldF j.succ) (fun j => newF j.succ) (fun j => u j.succ) ρe
      (index + 1) fired (fun j => hfin j.succ)
    rw [ih, List.map_append]
    congr 1
    simp only [freshPattern, Fin.val_zero, add_zero, hfresh]
    cases nrmFresh (floatReal (oldF 0)) (floatReal (newF 0)) index fired <;> simp

lemma selectedValues_all : ∀ {m : ℕ} (f : Fin m → Bool) (u : Fin m → ℝ), (∀ j, f j = true) →
    selectedValues f u = List.ofFn u
  | 0, _, _, _ => by simp [selectedValues]
  | m + 1, f, u, hf => by
    rw [selectedValues_succ, selectedValues_all (fun j => f j.succ) (fun j => u j.succ)
      (fun j => hf j.succ), hf 0, List.ofFn_succ]
    rfl

/-- Rounded exponential grid of a primitive NRM input: row `0` initializes, row
`l + 1` is the update after event `l`. Unused coordinates are never read. -/
noncomputable def nrmFloatExps {n K : ℕ} (ρe : ℝ → Binary64) (p : NRMRawInput n K) (l : ℕ) :
    Fin (n + 1) → Binary64 :=
  if l = 0 then fun j => ρe (p.1 j) else fun j => ρe (nrmRawFresh p (l - 1) j)

lemma nrmParse_float_schedule_tape {n : ℕ} (ratesF : ℕ → Fin (n + 1) → Binary64)
    (marks : ℕ → Fin (n + 1)) (K : ℕ) (ω : Streams) (ρe : ℝ → Binary64) (c0 : ℕ)
    (hfin : ∀ l j, ExecFloat.Binary.isFinite (ratesF l j) = true)
    (hω : (nrmInitReader (fun j => floatReal (ratesF 0 j))).rest ω = streamsDrop (n + 1) c0 ω) :
    ∀ count k, k + count ≤ K →
      nrmFloatTape ratesF (nrmFloatExps ρe (nrmParse (fun l j => floatReal (ratesF l j)) marks K ω))
        marks k count =
        (List.range (∑ i ∈ Finset.range count,
          nrmStepCount (fun l j => floatReal (ratesF l j)) marks (k + i))).map
          (fun r => ρe (ω (.inr (c0 + (∑ i ∈ Finset.range k,
            nrmStepCount (fun l j => floatReal (ratesF l j)) marks i) + r)))) := by
  intro count
  induction count with
  | zero => intro k _; simp [nrmFloatTape]
  | succ count ih =>
    intro k hk
    have he : nrmFloatExps ρe (nrmParse (fun l j => floatReal (ratesF l j)) marks K ω) (k + 1) =
        fun j => ρe (nrmRawFresh (nrmParse (fun l j => floatReal (ratesF l j)) marks K ω) k j) := by
      simp [nrmFloatExps]
    rw [nrmFloatTape, ih (k + 1) (by omega), he,
      updateTape_selected _ _ _ ρe 0 _ (fun j => ⟨hfin k j, hfin (k + 1) j⟩),
      nrmParse_fresh (fun l j => floatReal (ratesF l j)) marks K ω k (by omega)]
    change (selectedValues (freshPattern (fun j => floatReal (ratesF k j))
        (fun j => floatReal (ratesF (k + 1) j)) 0 (marks k).val)
      (fun j => (streamsDrop (∑ i ∈ Finset.range k, (n + 1))
        (∑ i ∈ Finset.range k, nrmStepCount (fun l j => floatReal (ratesF l j)) marks i)
          ((nrmInitReader (fun j => floatReal (ratesF 0 j))).rest ω))
          (nrmRowIndex (n + 1) (freshPattern (fun j => floatReal (ratesF k j))
            (fun j => floatReal (ratesF (k + 1) j)) 0 (marks k).val) 0 0 j))).map ρe ++ _ = _
    rw [selectedValues_row, hω, streamsDrop_drop]
    have hsum : ∑ i ∈ Finset.range (count + 1),
        nrmStepCount (fun l j => floatReal (ratesF l j)) marks (k + i) =
        nrmStepCount (fun l j => floatReal (ratesF l j)) marks k +
          ∑ i ∈ Finset.range count, nrmStepCount (fun l j => floatReal (ratesF l j)) marks (k + 1 + i) := by
      rw [Finset.sum_range_succ', add_comm]
      simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    have hprefix : ∑ i ∈ Finset.range (k + 1), nrmStepCount (fun l j => floatReal (ratesF l j)) marks i =
        ∑ i ∈ Finset.range k, nrmStepCount (fun l j => floatReal (ratesF l j)) marks i +
          nrmStepCount (fun l j => floatReal (ratesF l j)) marks k :=
      Finset.sum_range_succ _ _
    rw [hsum, hprefix, List.range_add, List.map_append, List.map_map, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro r _
      simp only [Function.comp_apply, streamsDrop, Sum.map_inr, zero_add]
    · apply List.map_congr_left
      intro r _
      simp only [Function.comp_apply]
      congr 3
      unfold nrmStepCount
      omega

section NRMFloat

variable {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
  (htransition : ∀ x i, mf.transition x i = mr.transition x i)
  (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
  (CF : FloatModelConsistency mf transition ratesF lowerF upperF) (initial : σ)
  (ρe : ℝ → Binary64) (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ) (fuel cap : ℕ) (save : Bool)

/-- Numerical certificate event of the coupled NRM simulations, with persistent float
and real absolute clocks along the realized real reaction word. -/
noncomputable def nrmFloatGood : Set Streams :=
  {ω | ∃ w : Fin (fuel + 1) → Fin (n + 1),
    ω ∈ nrmWordEvent transition (fun x j => floatReal (ratesF x j)) initial w ∧
    NRMTrajectoryConditions mf mr htransition (stateAlongWord transition initial (extendMarks w))
      (extendMarks w) (fun l => ratesF (stateAlongWord transition initial (extendMarks w) l))
      (nrmFloatExps ρe (nrmWordParse transition (fun x j => floatReal (ratesF x j)) initial w ω))
      (nrmRawExponentials (nrmWordParse transition (fun x j => floatReal (ratesF x j)) initial w ω))
      (fun l => CF.rates_eq _) (fun l => CF.transition_eq _ _) start hf sr hr δ η fuel cap save}

end NRMFloat

/-- On the NRM certificate event, the public FloatLib NRM simulator is trace-close to
the public real NRM simulator, both reading the same IID streams. -/
theorem nrm_float_iid_close {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (a b : ℕ) (hb : (n + 1) * (fuel + 1) ≤ b)
    (ω : Streams)
    (hω : ω ∈ nrmFloatGood mf mr htransition transition ratesF lowerF upperF CF initial ρe start hf
      sr hr δ η fuel cap save) :
    ∃ w : Fin (fuel + 1) → Fin (n + 1),
      ω ∈ nrmWordEvent transition (fun x j => floatReal (ratesF x j)) initial w ∧
      observeRun (simulate realArithmetic (tapeSource ℝ) mr .nrm initial sr hr (streamTape a b ω)
        fuel save cap) =
        holdingSimulationObservation mr (stateAlongWord transition initial (extendMarks w))
          (fun l j => floatReal (ratesF (stateAlongWord transition initial (extendMarks w) l) j))
          (extendMarks w) sr hr fuel save
          ((nrmRawHistory (fun l => completedRates (fun j =>
            floatReal (ratesF (stateAlongWord transition initial (extendMarks w) l) j)))
            (extendMarks w) (fuel + 1)
            (nrmWordParse transition (fun x j => floatReal (ratesF x j)) initial w ω)).1) ∧
      TraceClose δ
        (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .nrm initial start hf
          (floatStreamTape ρu ρe a b ω) fuel save cap))
        (observeRun (simulate realArithmetic (tapeSource ℝ) mr .nrm initial sr hr (streamTape a b ω)
          fuel save cap)) := by
  obtain ⟨w, hE, hcert⟩ := hω
  let rr := fun x j => floatReal (ratesF x j)
  let states := stateAlongWord transition initial (extendMarks w)
  let rates := fun l => ratesF (states l)
  let parse := nrmWordParse transition rr initial w ω
  have hreal := nrm_stream_driver_executes mr transition rr (fun x j => floatReal (lowerF x j))
    (fun x j => floatReal (upperF x j)) CR initial sr hr hsr fuel cap save a b hb w ω hE
  refine ⟨w, hE, hreal, ?_⟩
  have hpos : ∀ l j, 0 < floatReal (rates l j) := fun l j =>
    real_positive_of_flag _ (finite_of_valid _ (hcert.hv l j)) (hcert.hp l j)
  have hcompleted : (fun l => completedRates (fun j =>
      floatReal (ratesF (stateAlongWord transition initial (extendMarks w) l) j))) =
      (fun l j => floatReal (ratesF (stateAlongWord transition initial (extendMarks w) l) j)) := by
    funext l
    have hA : 0 < ∑ j, floatReal (ratesF (stateAlongWord transition initial (extendMarks w) l) j) :=
      Finset.sum_pos (fun j _ => hpos l j) Finset.univ_nonempty
    simp only [completedRates, hA, ite_true]
  have hreplay := nrm_real_replay_eq_holdings mr states rates (extendMarks w) hpos sr hr fuel save parse
  have hrun : observeRun (simulate realArithmetic (tapeSource ℝ) mr .nrm initial sr hr (streamTape a b ω)
      fuel save cap) = replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (nrmRealTimes rates (nrmRawExponentials parse) (extendMarks w) sr)
          (fun l => (extendMarks w l).val) 0 (fuel + 1)) := by
    rw [hreal]
    unfold nrmRealReplay at hreplay
    rw [hreplay, hcompleted]
  -- The float exponential tape is the rounded consumed stream prefix.
  let c0 := freshCount (n + 1) (freshPattern (fun _ => 0) (rr (states 0)) 0 0)
  let S := ∑ i ∈ Finset.range fuel, nrmStepCount (fun l j => rr (states l) j) (extendMarks w) i
  have hc0 : c0 ≤ n + 1 := freshCount_le _ _
  have hS : S ≤ (n + 1) * fuel := by
    calc S ≤ ∑ i ∈ Finset.range fuel, (n + 1) :=
          Finset.sum_le_sum (fun i _ => freshCount_le _ _)
      _ = (n + 1) * fuel := by simp [mul_comm]
  have hMb : c0 + S ≤ b := by nlinarith
  obtain ⟨rest, hrest⟩ := Nat.exists_eq_add_of_le hMb
  have hfin : ∀ l j, ExecFloat.Binary.isFinite (rates l j) = true := fun l j =>
    finite_of_valid _ (hcert.hv l j)
  have hω0 : (nrmInitReader (fun j => floatReal (rates 0 j))).rest ω = streamsDrop (n + 1) c0 ω := rfl
  have hsched := nrmParse_float_schedule_tape rates (extendMarks w) (fuel + 1) ω ρe c0 hfin hω0 fuel 0
    (by omega)
  simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add] at hsched
  have hp0 : ∀ j, 0 < rr (states 0) j := fun j => hpos 0 j
  have hall : ∀ j, freshPattern (fun _ => 0) (rr (states 0)) 0 0 j = true := by
    intro j
    simp [freshPattern, nrmFresh, hp0 j]
  have hinitF : List.ofFn (nrmFloatExps ρe parse 0) =
      (List.range c0).map (fun r => ρe (ω (.inr r))) := by
    have hsel := selectedValues_row (n + 1) (freshPattern (fun _ => 0) (rr (states 0)) 0 0) 0 0 ω
    rw [selectedValues_all _ _ hall] at hsel
    show List.ofFn (ρe ∘ (fun j => ω (nrmRowIndex (n + 1) (freshPattern (fun _ => 0) (rr (states 0)) 0 0)
      0 0 j))) = _
    rw [← List.map_ofFn, hsel, List.map_map]
    apply List.map_congr_left
    intro r _
    simp
  have htape : floatStreamTape ρu ρe a b ω =
      ⟨List.ofFn (fun i : Fin a => ρu (ω (.inl i))),
        List.ofFn (nrmFloatExps ρe parse 0) ++
          (nrmFloatTape rates (nrmFloatExps ρe parse) (extendMarks w) 0 fuel ++
            (List.range rest).map (fun r => ρe (ω (.inr (c0 + S + r)))))⟩ := by
    have hsched' : nrmFloatTape rates (nrmFloatExps ρe parse) (extendMarks w) 0 fuel =
        (List.range S).map (fun r => ρe (ω (.inr (c0 + r)))) := hsched
    rw [hinitF, hsched']
    simp only [floatStreamTape]
    congr 1
    rw [ofFn_eq_range_map b (fun i => ρe (ω (.inr i))), hrest, List.range_add, List.range_add,
      List.map_append, List.map_append, List.map_map, List.map_map, List.append_assoc]
    rfl
  have hinit : initial = states 0 := rfl
  rw [hrun, htape, hinit]
  exact nrm_float_trajectory_close_from mf mr htransition states (extendMarks w) rates
    (nrmFloatExps ρe parse) (nrmRawExponentials parse) (fun l => CF.rates_eq _)
    (fun l => CF.transition_eq _ _) start hf sr hr δ η fuel cap save _ _ hcert.hp hcert.hv hcert.hi
    hcert.hc hcert.hcacheFinite hcert.hgap hcert.hinc hcert.hrinc hcert.hbudget hcert.hvalid hcert.hstart
    hcert.hhf hcert.hh hcert.h0 hcert.hmargin

lemma nrm_word_observation_law {σ X : Type} [MeasurableSpace X] {n : ℕ} (model : Model ℝ σ)
    (transition : σ → Fin (n + 1) → σ) (rates : σ → Fin (n + 1) → ℝ) (hr : ∀ x j, 0 ≤ rates x j)
    (initial : σ) (start horizon : ℝ) (fuel : ℕ) (save : Bool)
    (observable : Except Error (TraceObservation ℝ σ) → X) (w : Fin (fuel + 1) → Fin (n + 1))
    (hobs : Measurable (fun ts => observable (holdingSimulationObservation model
      (stateAlongWord transition initial (extendMarks w))
      (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w)
      start horizon fuel save ts))) :
    (iidStreams.restrict (nrmWordEvent transition rates initial w)).map (fun ω => observable
      (holdingSimulationObservation model (stateAlongWord transition initial (extendMarks w))
        (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w)
        start horizon fuel save ((nrmRawHistory
          (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks w) l)))
          (extendMarks w) (fuel + 1) (nrmWordParse transition rates initial w ω)).1))) =
    (targetWordLaw (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks w) l)))
      (extendMarks w) (fuel + 1)).map (fun ts => observable (holdingSimulationObservation model
        (stateAlongWord transition initial (extendMarks w))
        (fun l => rates (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w)
        start horizon fuel save ts)) := by
  have hmh := (measurable_nrmRawHistory
    (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks w) l)))
    (extendMarks w) (fuel + 1)).fst
  have hparse : Measurable (nrmWordParse transition rates initial w) :=
    measurable_nrmParse (fun l => rates (stateAlongWord transition initial (extendMarks w) l))
      (extendMarks w) (fuel + 1)
  have h1 := Measure.map_map (μ := iidStreams.restrict (nrmWordEvent transition rates initial w)) hobs
    (hmh.comp hparse)
  have h2 := Measure.map_map (μ := iidStreams.restrict (nrmWordEvent transition rates initial w)) hmh hparse
  rw [← h2, nrmWordEvent_branch, nrmWord_holding_law _ _ _ hr] at h1
  exact h1.symm

/-- FloatLib NRM simulations on rounded IID streams approximate the exact target law.
`β` is the outer probability that the NRM numerical certificate fails along the
realized reaction word, including every persistent cache comparison. -/
theorem nrm_float_iid_law_bounds {σ ι : Type} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (a b : ℕ) (hb : (n + 1) * (fuel + 1) ≤ b)
    (T : Except Error (TraceObservation ℝ σ) → ℝ) (Tf : Except Error (TraceObservation Binary64 σ) → ℝ)
    (I : Except Error (TraceObservation ℝ σ) → ι) (If : Except Error (TraceObservation Binary64 σ) → ι)
    (εobs : ℝ) (hobs : ∀ f r, TraceClose δ f r → |Tf f - T r| ≤ εobs ∧ If f = I r)
    (hM : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts =>
        let r := holdingSimulationObservation mr states (fun l j => floatReal (ratesF (states l) j))
          marks sr hr fuel save ts
        (T r, I r)))
    (i : ι) (t : ℝ) :
    let Ff := fun ω => observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .nrm initial
      start hf (floatStreamTape ρu ρe a b ω) fuel save cap)
    let target := targetSimulationLaw mr transition (fun x j => floatReal (ratesF x j)) initial sr hr fuel
      save (fun r => (T r, I r))
    let β := iidStreams (nrmFloatGood mf mr htransition transition ratesF lowerF upperF CF initial ρe start
      hf sr hr δ η fuel cap save)ᶜ
    target (jointTail (t + εobs) i) ≤ iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} + β ∧
    iidStreams {ω | t < Tf (Ff ω) ∧ If (Ff ω) = i} ≤ target (jointTail (t - εobs) i) + β := by
  intro Ff target β
  let rr := fun x j => floatReal (ratesF x j)
  let E := fun w : Fin (fuel + 1) → Fin (n + 1) => nrmWordEvent transition rr initial w
  let G := fun (w : Fin (fuel + 1) → Fin (n + 1)) (ω : Streams) =>
    let r := holdingSimulationObservation mr (stateAlongWord transition initial (extendMarks w))
      (fun l j => rr (stateAlongWord transition initial (extendMarks w) l) j) (extendMarks w) sr hr fuel
      save ((nrmRawHistory (fun l => completedRates (rr (stateAlongWord transition initial (extendMarks w) l)))
        (extendMarks w) (fuel + 1) (nrmWordParse transition rr initial w ω)).1)
    (T r, I r)
  have hG : ∀ w, Measurable (G w) := fun w =>
    (hM w).comp ((measurable_nrmRawHistory _ _ _).fst.comp
      (measurable_nrmParse (fun l => rr (stateAlongWord transition initial (extendMarks w) l))
        (extendMarks w) (fuel + 1)))
  have htarget : target = Measure.sum (fun w => (iidStreams.restrict (E w)).map (G w)) := by
    simp only [target, targetSimulationLaw]
    congr 1
    funext w
    exact (nrm_word_observation_law mr transition rr CR.nonnegative initial sr hr fuel save
      (fun r => (T r, I r)) w (hM w)).symm
  apply word_coupling_tail_bounds E (fun w => measurableSet_nrmWordEvent _ _ _ w)
    (nrmWordEvent_disjoint _ _ _ (fuel + 1)) (nrmWordEvent_total _ _ _ CR.nonnegative (fuel + 1))
    G hG target htarget Ff Tf If _ εobs
  intro w ω ⟨hEw, hgood⟩
  obtain ⟨w', hE', hreal, hclose⟩ := nrm_float_iid_close mf mr htransition transition ratesF lowerF
    upperF CF CR initial ρu ρe start hf sr hr δ η hsr fuel cap save a b hb ω hgood
  have hw : w' = w := by
    by_contra hne
    exact (Set.disjoint_left.mp (nrmWordEvent_disjoint transition rr initial (fuel + 1) hne)) hE' hEw
  subst hw
  have h := hobs _ _ hclose
  rw [hreal] at h
  exact h

end JumpProcessesLean.Proofs
