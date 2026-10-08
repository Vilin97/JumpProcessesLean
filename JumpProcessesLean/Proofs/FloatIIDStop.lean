import JumpProcessesLean.Proofs.NRMFloatMasked

/-!
# FloatLib simulations coupled to the IID streams, through absorbing states

These theorems extend `FloatIID.lean`. Every certificate carries a stop index
`m ≤ fuel + 1`. Steps `k < m` carry the one-event numerical certificates. If
`m ≤ fuel`, the realized word reaches an absorbing state at step `m`, and both public
simulators must stop there. The NRM certificate uses the masked FloatLib cache, so
channels may be inactive, deactivated or reactivated along the word.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- A packet replay stopped at an absorbing step `m` is the holding-time replay. -/
lemma packet_real_replay_stop_eq_holdings {σ γ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (clock : Nat → γ → ℝ) (fallback : γ) (start horizon : ℝ) (fuel m : Nat) (save : Bool)
    (hstop : m ≤ fuel + 1) (hA : ∀ l, l < m → 0 < ∑ j, rates l j)
    (hZ : m ≤ fuel → ¬0 < ∑ j, rates m j) (p : Fin (fuel + 1) → γ) :
    replayEvents realArithmetic model horizon save fuel (states 0) start 0 #[(start, states 0)]
      (scheduledEvents (realTimeSchedule clock (rawChronological fallback p) start)
        (fun l => (marks l).val) 0 m) =
      holdingSimulationObservation model states rates marks start horizon fuel save
        (rawWordHoldings clock (fuel + 1) p) := by
  by_cases hm : m ≤ fuel
  · unfold holdingSimulationObservation
    have h := scheduled_events_eq_nrm_absorb rates
      (holdingSchedule (rawWordHoldings clock (fuel + 1) p)) marks
      (realTimeSchedule clock (rawChronological fallback p) start) m hA (hZ hm) fuel 0 (by omega)
      (by omega)
    rw [Nat.sub_zero] at h
    rw [h, schedule_events_times_congr rates _ _ marks _ _ (fuel + 1)
      (fun l hl => packet_real_times_eq_holdings clock fallback marks p start l hl) 0 fuel (by omega)]
  · have hm' : m = fuel + 1 := by omega
    subst hm'
    exact packet_real_replay_eq_holdings model states rates marks clock fallback start horizon fuel save
      (fun l hl => hA l (by omega)) p

/-! ### Direct -/

section DirectStop

variable {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
  (htransition : ∀ x i, mf.transition x i = mr.transition x i)
  (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
  (CF : FloatModelConsistency mf transition ratesF lowerF upperF) (initial : σ)
  (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ) (fuel cap : ℕ) (save : Bool)

/-- Direct certificate event with a stop index: the realized real word carries the
Direct certificate up to step `m`, where it reaches an absorbing state if `m ≤ fuel`. -/
noncomputable def directFloatStopGood : Set Streams :=
  {ω | (∀ x, ω x ∈ Ioo (0 : ℝ) 1) ∧ ∃ w : Fin (fuel + 1) → Fin (n + 1),
    ω ∈ directWordEvent transition (fun x j => floatReal (ratesF x j)) initial w ∧
    ∃ m, DirectStopConditions mf mr htransition (stateAlongWord transition initial (extendMarks w))
      (fun l => (extendMarks w l).val)
      (fun l => Array.ofFn (ratesF (stateAlongWord transition initial (extendMarks w) l)))
      (fun _ => CF.rates_eq _) (fun _ => CF.transition_eq _ _) (fun _ p => ρe p.1) (fun _ p => ρu p.2)
      (rawChronological (1 / 2, 1 / 2) (directParse (fuel + 1) ω)) start hf sr hr ε d δ η fuel cap m
      save ∧
    (m ≤ fuel → ¬0 < ∑ j, floatReal (ratesF (stateAlongWord transition initial (extendMarks w) m) j))}

end DirectStop

/-- On the stopped Direct certificate event, the public FloatLib Direct simulator is
trace-close to the public real Direct simulator, both reading the same IID streams. -/
theorem direct_float_iid_stop_close {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (c e : ℕ) (ω : Streams)
    (hω : ω ∈ directFloatStopGood mf mr htransition transition ratesF lowerF upperF CF initial ρu ρe start
      hf sr hr ε d δ η fuel cap save) :
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
  obtain ⟨hcoord, w, hE, m, hcert, hZ⟩ := hω
  let states := stateAlongWord transition initial (extendMarks w)
  let rates := fun l => Array.ofFn (ratesF (states l))
  let source := rawChronological (1 / 2, 1 / 2) (directParse (fuel + 1) ω)
  have hreal := direct_stream_driver_executes mr transition (fun x j => floatReal (ratesF x j))
    (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)) CR initial sr hr hsr fuel
    cap save c e w ω hcoord hE
  refine ⟨w, hE, hreal, ?_⟩
  have hA : ∀ l, l < m → 0 < ∑ j, floatReal (ratesF (states l) j) := by
    intro l hl
    have h := hcert.hA l hl
    rwa [sum_floatReal_ofFn] at h
  -- The real public run is the stopped replay of the real certificate schedule.
  have hreplay : holdingSimulationObservation mr states (fun l j => floatReal (ratesF (states l) j))
      (extendMarks w) sr hr fuel save
      (rawWordHoldings (directWordClock transition (fun x j => floatReal (ratesF x j)) initial w)
        (fuel + 1) (directParse (fuel + 1) ω)) =
      replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (directRealClock rates) source sr)
          (fun l => (extendMarks w l).val) 0 m) := by
    rw [← packet_real_replay_stop_eq_holdings mr states (fun l j => floatReal (ratesF (states l) j))
      (extendMarks w) _ (1 / 2, 1 / 2) sr hr fuel m save hcert.stop hA hZ]
    congr 1
    apply scheduledEvents_congr
    intro l _ hl
    apply realTimeSchedule_congr _ _ _ _ m _ l (by omega)
    intro k hk
    exact (direct_real_clock_eq_word transition ratesF initial w k (hcert.hA k hk) _).symm
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
  exact direct_float_trajectory_close_stop mf mr htransition states (fun l => (extendMarks w l).val) rates
    (fun l => CF.rates_eq _) (fun l => CF.transition_eq _ _) (fun _ p => ρe p.1) (fun _ p => ρu p.2) source
    _ start hf sr hr ε d δ η fuel cap m save hcert

/-- FloatLib Direct simulations on rounded IID streams approximate the exact target
law, through absorbing states. `β` is the outer probability that the stopped Direct
certificate fails along the realized reaction word. -/
theorem direct_float_iid_stop_law_bounds {σ ι : Type} [MeasurableSpace ι] [MeasurableSingletonClass ι]
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
    let β := iidStreams (directFloatStopGood mf mr htransition transition ratesF lowerF upperF CF initial
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
  obtain ⟨w', hE', hreal, hclose⟩ := direct_float_iid_stop_close mf mr htransition transition ratesF
    lowerF upperF CF CR initial ρu ρe start hf sr hr ε d δ η hsr fuel cap save c e ω hgood
  have hw : w' = w := by
    by_contra hne
    exact (Set.disjoint_left.mp (directWordEvent_disjoint transition rr initial (fuel + 1) hne)) hE' hEw
  subst hw
  have h := hobs _ _ hclose
  rw [hreal] at h
  exact h

/-! ### Capped RSSA -/

section RSSAStop

variable {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
  (htransition : ∀ x i, mf.transition x i = mr.transition x i)
  (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
  (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
  (hbv : ∀ x j, 0 ≤ floatReal (lowerF x j) ∧ floatReal (lowerF x j) ≤ floatReal (ratesF x j) ∧
    floatReal (ratesF x j) ≤ floatReal (upperF x j))
  (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ) (fuel cap : ℕ)
  (save : Bool)

/-- Capped RSSA certificate event with a stop index. -/
noncomputable def rssaFloatStopGood : Set Streams :=
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
    ∃ m, RSSAStopConditions mf mr htransition (stateAlongWord transition initial (extendMarks w))
      (fun l => (extendMarks w l).val)
      (fun l => Array.ofFn (ratesF (stateAlongWord transition initial (extendMarks w) l)))
      (fun l => ⟨Array.ofFn (lowerF (stateAlongWord transition initial (extendMarks w) l)),
        Array.ofFn (upperF (stateAlongWord transition initial (extendMarks w) l))⟩)
      (fun _ => CF.rates_eq _) (fun _ => CF.bounds_eq _) (fun _ => CF.transition_eq _ _)
      (rssaFloatExp ρe) (rssaFloatSel ρu) (rssaFloatAcc ρu)
      (rawChronological ⟨(0, 0), (fun _ => 1 / 2, fun _ => (1 / 2, 1 / 2))⟩
        (rssaWordParse transition (fun x j => floatReal (ratesF x j)) (fun x j => floatReal (lowerF x j))
          (fun x j => floatReal (upperF x j)) hbv initial w ω))
      start hf sr hr ε d δ η fuel cap m save ∧
    (m ≤ fuel → ¬0 < ∑ j, floatReal (ratesF (stateAlongWord transition initial (extendMarks w) m) j))}

end RSSAStop

/-- On the stopped RSSA certificate event, the public FloatLib capped RSSA simulator is
trace-close to the public real capped RSSA simulator on the same IID streams. -/
theorem rssa_float_iid_stop_close {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (a b : ℕ)
    (ha : 2 * cap * (fuel + 1) ≤ a) (hb : cap * (fuel + 1) ≤ b) (ω : Streams)
    (hω : ω ∈ rssaFloatStopGood mf mr htransition transition ratesF lowerF upperF CF CR.bounds_valid
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
  obtain ⟨hcoord, w, hgoodR, hE, hcap, m, hcert, hZ⟩ := hω
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
  -- Every certified step has a positive real total rate.
  have hA : ∀ l, l < m → 0 < ∑ j, rr (states l) j := by
    intro l hl
    have hg := (hcert.hg l hl).2.2.2
    simp only [Array.toList_ofFn, List.map_ofFn] at hg
    exact proposalBranch_total_pos (fun j => rr (states l) j) (fun j => lr (states l) j)
      (fun j => ur (states l) j) (fun j => CR.bounds_valid _ j) _ _ _ hg
  have hclock : ∀ l, l < m → ∀ p, rssaStoppingTime (n := n + 1)
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
          (fun l => (extendMarks w l).val) 0 m) := by
    rw [← packet_real_replay_stop_eq_holdings mr states (fun l j => rr (states l) j) (extendMarks w) _
      fallback sr hr fuel m save hcert.stop hA hZ]
    congr 1
    apply scheduledEvents_congr
    intro l _ hl
    apply realTimeSchedule_congr _ _ _ _ m _ l (by omega)
    intro k hk
    exact hclock k hk _
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
  have hrun : observeRun (simulate realArithmetic (tapeSource ℝ) mr .rssa initial sr hr (streamTape a b ω)
      fuel save cap) = replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule (rssaRealClock bounds) source sr)
          (fun l => (extendMarks w l).val) 0 m) := hreal.trans hreplay
  rw [hrun, htape, hinit]
  exact rssa_float_trajectory_close_stop mf mr htransition states (fun l => (extendMarks w l).val) rates
    bounds (fun l => CF.rates_eq _) (fun l => CF.bounds_eq _) (fun l => CF.transition_eq _ _)
    (rssaFloatExp ρe) (rssaFloatSel ρu) (rssaFloatAcc ρu) source tail start hf sr hr ε d δ η fuel cap m save
    hcert

/-- FloatLib capped RSSA simulations on rounded IID streams approximate the exact
target law, through absorbing states. `β` is the outer probability that the realized
first-success blocks exceed the cap or violate the stopped RSSA certificate. -/
theorem rssa_float_iid_stop_law_bounds {σ ι : Type} [MeasurableSpace ι] [MeasurableSingletonClass ι]
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
    let β := iidStreams (rssaFloatStopGood mf mr htransition transition ratesF lowerF upperF CF
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
  obtain ⟨w', hE', hreal, hclose⟩ := rssa_float_iid_stop_close mf mr htransition transition ratesF lowerF
    upperF CF CR initial ρu ρe start hf sr hr ε d δ η hsr fuel cap save a b ha hb ω hgood
  have hw : w' = w := by
    by_contra hne
    exact (Set.disjoint_left.mp (rssaWordEvent_disjoint transition rr lr ur CR.bounds_valid initial
      (fuel + 1) hne)) hE' hEw
  subst hw
  have h := hobs _ _ hclose
  rw [hreal] at h
  exact h

/-! ### Masked NRM -/

lemma nrmScheduleTime_congr {n : Nat} (c c' : Nat → Fin n → ℝ) (marks : Nat → Fin n) (start : ℝ) :
    ∀ l, (∀ k, k < l → c k = c' k) → nrmScheduleTime c marks start l = nrmScheduleTime c' marks start l := by
  intro l
  induction l with
  | zero => intro _; rfl
  | succ l ih =>
    intro h
    rw [nrmScheduleTime, nrmScheduleTime, ih (fun k hk => h k (by omega)), h l (by omega)]

/-- The exact masked real clocks are the persistent cache of the primitive probability
proof, for every channel active at the current step. -/
lemma nrm_real_clocksM_raw_schedule {n k : Nat} (rates : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (p : NRMRawInput n k) (start : ℝ) (L : Nat)
    (hact : ∀ l, l < L → 0 < floatReal (rates l (marks l))) :
    ∀ l, l ≤ L → ∀ j, 0 < floatReal (rates l j) →
      nrmRealClocksM rates (nrmRawExponentials p) marks start l j =
        nrmScheduleTime (nrmScheduleCache (fun l j => floatReal (rates l j)) marks p.1 (nrmRawFresh p))
          marks start l +
        nrmScheduleCache (fun l j => floatReal (rates l j)) marks p.1 (nrmRawFresh p) l j := by
  intro l
  induction l with
  | zero =>
    intro _ j hj
    simp [nrmRealClocksM, nrmRawExponentials, nrmScheduleTime, nrmScheduleCache, ghostRate_of_positive hj,
      exponentialClock]
  | succ l ih =>
    intro hl j hj
    have hw := ih (by omega) (marks l) (hact l (by omega))
    rw [nrmRealClocksM, nrmScheduleTime, nrmScheduleCache]
    simp only [updatedRealClock, nrmRawExponentials, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    by_cases hjm : j = marks l
    · subst j
      simp only [ne_eq, not_true_eq_false, false_and, ite_false, hw, maskedResidual, keepClock,
        ghostRate_of_positive hj, exponentialClock]
    · by_cases hold : 0 < floatReal (rates l j)
      · have hk : keepClock (fun j => floatReal (rates l j)) (fun j => floatReal (rates (l + 1) j))
            (marks l) j := ⟨hjm, hold, hj⟩
        simp only [ne_eq, hjm, not_false_eq_true, hold, and_self, ite_true, hw, ih (by omega) j hold,
          maskedResidual, hk]
        ring
      · have hk : ¬keepClock (fun j => floatReal (rates l j)) (fun j => floatReal (rates (l + 1) j))
            (marks l) j := fun h => hold h.2.1
        simp only [ne_eq, hjm, not_false_eq_true, hold, and_false, ite_false, hw, maskedResidual, hk,
          ghostRate_of_positive hj, exponentialClock]

lemma nrm_real_timesM_raw_schedule {n k : Nat} (rates : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (p : NRMRawInput n k) (start : ℝ) (L : Nat)
    (hact : ∀ l, l < L → 0 < floatReal (rates l (marks l))) :
    ∀ l, l ≤ L → nrmRealTimesM rates (nrmRawExponentials p) marks start l =
      nrmScheduleTime (nrmScheduleCache (fun l j => floatReal (rates l j)) marks p.1 (nrmRawFresh p))
        marks start l := by
  intro l hl
  cases l with
  | zero => rfl
  | succ l =>
    rw [nrmRealTimesM, nrm_real_clocksM_raw_schedule rates marks p start L hact l (by omega) (marks l)
      (hact l (by omega))]
    rfl

/-- The masked real replay, stopped at an absorbing step `m`, is the holding-time replay
of the real target law. -/
lemma nrm_masked_real_replay_eq_holdings {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → Binary64) (marks : Nat → Fin (n + 1))
    (hnn : ∀ l j, 0 ≤ floatReal (rates l j)) (start horizon : ℝ) (fuel m : Nat) (save : Bool)
    (hstop : m ≤ fuel + 1) (hact : ∀ l, l < m → 0 < floatReal (rates l (marks l)))
    (hZ : m ≤ fuel → ∀ j, ¬0 < floatReal (rates m j)) (p : NRMRawInput n (fuel + 1)) :
    replayEvents realArithmetic model horizon save fuel (states 0) start 0 #[(start, states 0)]
      (scheduledEvents (nrmRealTimesM rates (nrmRawExponentials p) marks start)
        (fun l => (marks l).val) 0 m) =
      holdingSimulationObservation model states (fun l j => floatReal (rates l j)) marks start horizon fuel
        save (nrmRawHistory (fun l => completedRates (fun j => floatReal (rates l j))) marks (fuel + 1) p).1 := by
  have hA : ∀ l, l < m → 0 < ∑ j, floatReal (rates l j) := fun l hl =>
    lt_of_lt_of_le (hact l hl) (Finset.single_le_sum (fun j _ => hnn l j) (Finset.mem_univ _))
  have hcomp : ∀ l, l < m → completedRates (fun j => floatReal (rates l j)) = fun j => floatReal (rates l j) :=
    fun l hl => by simp only [completedRates, hA l hl, ↓reduceIte]
  let H := (nrmRawHistory (fun l => completedRates (fun j => floatReal (rates l j))) marks (fuel + 1) p).1
  have htimes : ∀ l, l ≤ m → nrmRealTimesM rates (nrmRawExponentials p) marks start l =
      nrmScheduleTime (holdingSchedule H) marks start l := by
    intro l hl
    rw [nrm_real_timesM_raw_schedule rates marks p start m hact l hl,
      ← holding_schedule_times (fun l => completedRates (fun j => floatReal (rates l j))) marks p start l
        (by omega)]
    apply nrmScheduleTime_congr
    intro k hk
    exact nrmScheduleCache_congr _ _ _ _ _ _ _ k (fun i hi => (hcomp i (by omega)).symm)
      (fun _ _ => rfl) (fun _ _ => rfl)
  rw [scheduledEvents_congr _ (nrmScheduleTime (holdingSchedule H) marks start) _ m 0
    (fun l _ hl => htimes l (by omega))]
  unfold holdingSimulationObservation
  by_cases hm : m ≤ fuel
  · have hZ' : ¬0 < ∑ j, floatReal (rates m j) :=
      not_lt.mpr (Finset.sum_nonpos (fun j _ => not_lt.mp (hZ hm j)))
    have h := scheduled_events_eq_nrm_absorb (fun l j => floatReal (rates l j)) (holdingSchedule H) marks
      (nrmScheduleTime (holdingSchedule H) marks start) m hA hZ' fuel 0 (by omega) (by omega)
    rw [Nat.sub_zero] at h
    rw [h]
  · have hm' : m = fuel + 1 := by omega
    subst hm'
    rw [scheduled_events_eq_nrm (fun l j => floatReal (rates l j)) (holdingSchedule H) marks _ fuel
      (fun l hl => hA l (by omega)) 0 fuel (by omega)]

/-- Native masked initialization reads the rounded exponential draws of the active
channels, in channel order. -/
lemma nrmFloatInitTape_selected : ∀ {m : ℕ} (rates : Fin m → Binary64) (u : Fin m → ℝ)
    (ρe : ℝ → Binary64) (index fired : ℕ), (∀ j, ExecFloat.Binary.isFinite (rates j) = true) →
    nrmFloatInitTape rates (fun j => ρe (u j)) =
      (selectedValues (freshPattern (fun _ => 0) (fun j => floatReal (rates j)) index fired) u).map ρe
  | 0, _, _, _, _, _, _ => by simp [nrmFloatInitTape, selectedValues]
  | m + 1, rates, u, ρe, index, fired, hfin => by
    rw [nrmFloatInitTape_succ, selectedValues_succ, freshPattern_tail]
    have ih := nrmFloatInitTape_selected (fun j => rates j.succ) (fun j => u j.succ) ρe (index + 1) fired
      (fun j => hfin j.succ)
    rw [ih, List.map_append]
    congr 1
    rw [float_lt_zero_decide _ (hfin 0)]
    simp only [freshPattern, nrmFresh, Fin.val_zero, add_zero, lt_irrefl, not_false_eq_true, or_true,
      and_true]
    by_cases h : 0 < floatReal (rates 0) <;> simp [h]

section NRMMasked

variable {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
  (htransition : ∀ x i, mf.transition x i = mr.transition x i)
  (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
  (CF : FloatModelConsistency mf transition ratesF lowerF upperF) (initial : σ)
  (ρe : ℝ → Binary64) (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ) (fuel cap : ℕ) (save : Bool)

/-- Masked NRM certificate event: the realized real reaction word carries the masked
FloatLib cache certificate up to a stop index. Channels may be inactive. -/
noncomputable def nrmFloatMaskedGood : Set Streams :=
  {ω | ∃ w : Fin (fuel + 1) → Fin (n + 1),
    ω ∈ nrmWordEvent transition (fun x j => floatReal (ratesF x j)) initial w ∧
    ∃ m, NRMMaskedConditions mf mr htransition (stateAlongWord transition initial (extendMarks w))
      (extendMarks w) (fun l => ratesF (stateAlongWord transition initial (extendMarks w) l))
      (nrmFloatExps ρe (nrmWordParse transition (fun x j => floatReal (ratesF x j)) initial w ω))
      (nrmRawExponentials (nrmWordParse transition (fun x j => floatReal (ratesF x j)) initial w ω))
      (fun _ => CF.rates_eq _) (fun _ => CF.transition_eq _ _) start hf sr hr δ η fuel cap m save}

end NRMMasked

/-- On the masked NRM certificate event, the public FloatLib NRM simulator is
trace-close to the public real NRM simulator, both reading the same IID streams. -/
theorem nrm_float_iid_masked_close {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (CR : ModelConsistency mr transition (fun x j => floatReal (ratesF x j))
      (fun x j => floatReal (lowerF x j)) (fun x j => floatReal (upperF x j)))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ)
    (hsr : sr < hr) (fuel cap : ℕ) (save : Bool) (a b : ℕ) (hb : (n + 1) * (fuel + 1) ≤ b)
    (ω : Streams)
    (hω : ω ∈ nrmFloatMaskedGood mf mr htransition transition ratesF lowerF upperF CF initial ρe start hf
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
  obtain ⟨w, hE, m, hcert⟩ := hω
  let rr := fun x j => floatReal (ratesF x j)
  let states := stateAlongWord transition initial (extendMarks w)
  let rates := fun l => ratesF (states l)
  let parse := nrmWordParse transition rr initial w ω
  have hreal := nrm_stream_driver_executes mr transition rr (fun x j => floatReal (lowerF x j))
    (fun x j => floatReal (upperF x j)) CR initial sr hr hsr fuel cap save a b hb w ω hE
  refine ⟨w, hE, hreal, ?_⟩
  have hfin : ∀ l j, ExecFloat.Binary.isFinite (rates l j) = true := fun l j =>
    finite_of_valid _ (hcert.hv l j)
  have hZ : m ≤ fuel → ∀ j, ¬0 < floatReal (rates m j) := by
    intro hm j hpos
    have h := hcert.absorb hm j
    rw [float_lt_zero_decide _ (hfin m j)] at h
    exact absurd hpos (of_decide_eq_false h)
  have hrun : observeRun (simulate realArithmetic (tapeSource ℝ) mr .nrm initial sr hr (streamTape a b ω)
      fuel save cap) = replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (nrmRealTimesM rates (nrmRawExponentials parse) (extendMarks w) sr)
          (fun l => (extendMarks w l).val) 0 m) := by
    rw [hreal]
    exact (nrm_masked_real_replay_eq_holdings mr states rates (extendMarks w) (fun l j => CR.nonnegative _ j)
      sr hr fuel m save hcert.stop hcert.hactive hZ parse).symm
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
  have hω0 : (nrmInitReader (fun j => floatReal (rates 0 j))).rest ω = streamsDrop (n + 1) c0 ω := rfl
  have hsched := nrmParse_float_schedule_tape rates (extendMarks w) (fuel + 1) ω ρe c0 hfin hω0 fuel 0
    (by omega)
  simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add] at hsched
  have hinitF : nrmFloatInitTape (rates 0) (nrmFloatExps ρe parse 0) =
      (List.range c0).map (fun r => ρe (ω (.inr r))) := by
    have hsel := selectedValues_row (n + 1) (freshPattern (fun _ => 0) (rr (states 0)) 0 0) 0 0 ω
    have hinit := nrmFloatInitTape_selected (rates 0)
      (fun j => ω (nrmRowIndex (n + 1) (freshPattern (fun _ => 0) (rr (states 0)) 0 0) 0 0 j)) ρe 0 0
      (hfin 0)
    show nrmFloatInitTape (rates 0)
      (fun j => ρe (ω (nrmRowIndex (n + 1) (freshPattern (fun _ => 0) (rr (states 0)) 0 0) 0 0 j))) = _
    rw [hinit]
    change (selectedValues (freshPattern (fun _ => 0) (rr (states 0)) 0 0) _).map ρe = _
    rw [hsel, List.map_map]
    apply List.map_congr_left
    intro r _
    simp
  have htape : floatStreamTape ρu ρe a b ω =
      ⟨List.ofFn (fun i : Fin a => ρu (ω (.inl i))),
        nrmFloatInitTape (rates 0) (nrmFloatExps ρe parse 0) ++
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
  exact nrm_float_masked_trajectory_close mf mr htransition states (extendMarks w) rates
    (nrmFloatExps ρe parse) (nrmRawExponentials parse) (fun l => CF.rates_eq _)
    (fun l => CF.transition_eq _ _) start hf sr hr δ η fuel cap m save _ _ hcert

/-- FloatLib NRM simulations on rounded IID streams approximate the exact target law,
with inactive channels and absorbing states. `β` is the outer probability that the
masked NRM certificate fails along the realized reaction word. -/
theorem nrm_float_iid_masked_law_bounds {σ ι : Type} [MeasurableSpace ι] [MeasurableSingletonClass ι]
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
    let β := iidStreams (nrmFloatMaskedGood mf mr htransition transition ratesF lowerF upperF CF initial ρe
      start hf sr hr δ η fuel cap save)ᶜ
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
  obtain ⟨w', hE', hreal, hclose⟩ := nrm_float_iid_masked_close mf mr htransition transition ratesF lowerF
    upperF CF CR initial ρu ρe start hf sr hr δ η hsr fuel cap save a b hb ω hgood
  have hw : w' = w := by
    by_contra hne
    exact (Set.disjoint_left.mp (nrmWordEvent_disjoint transition rr initial (fuel + 1) hne)) hE' hEw
  subst hw
  have h := hobs _ _ hclose
  rw [hreal] at h
  exact h

/-! ### The stopped and masked events contain the positive-rate events -/

lemma directFloatGood_subset_stop {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF) (initial : σ)
    (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ) (fuel cap : ℕ) (save : Bool) :
    directFloatGood mf mr htransition transition ratesF lowerF upperF CF initial ρu ρe start hf sr hr ε d δ η
        fuel cap save ⊆
      directFloatStopGood mf mr htransition transition ratesF lowerF upperF CF initial ρu ρe start hf sr hr
        ε d δ η fuel cap save := by
  rintro ω ⟨hcoord, w, hE, hcert⟩
  refine ⟨hcoord, w, hE, fuel + 1, ?_, fun h => absurd h (by omega)⟩
  exact
    { stop := le_rfl
      hA := fun k _ => hcert.hA k (by omega)
      hg := fun k _ => hcert.hg k (by omega)
      hc := fun k _ => hcert.hc k (by omega)
      absorbValid := fun h => absurd h (by omega)
      absorbFinite := fun h => absurd h (by omega)
      absorbZero := fun h => absurd h (by omega)
      hvalid := hcert.hvalid
      hstart := hcert.hstart
      hhf := hcert.hhf
      hh := hcert.hh
      h0 := hcert.h0
      hd := hcert.hd
      hbudget := hcert.hbudget
      hmargin := fun k _ => hcert.hmargin k (by omega) }

lemma rssaFloatGood_subset_stop {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF)
    (hbv : ∀ x j, 0 ≤ floatReal (lowerF x j) ∧ floatReal (lowerF x j) ≤ floatReal (ratesF x j) ∧
      floatReal (ratesF x j) ≤ floatReal (upperF x j))
    (initial : σ) (ρu ρe : ℝ → Binary64) (start hf : Binary64) (sr hr ε d δ η : ℝ) (fuel cap : ℕ)
    (save : Bool) :
    rssaFloatGood mf mr htransition transition ratesF lowerF upperF CF hbv initial ρu ρe start hf sr hr ε d δ
        η fuel cap save ⊆
      rssaFloatStopGood mf mr htransition transition ratesF lowerF upperF CF hbv initial ρu ρe start hf sr hr
        ε d δ η fuel cap save := by
  rintro ω ⟨hcoord, w, hgoodR, hE, hcap, hcert⟩
  refine ⟨hcoord, w, hgoodR, hE, hcap, fuel + 1, ?_, fun h => absurd h (by omega)⟩
  exact
    { stop := le_rfl
      hupper := fun k _ => hcert.hupper k (by omega)
      hB := fun k _ => hcert.hB k (by omega)
      hg := fun k _ => hcert.hg k (by omega)
      hc := fun k _ => hcert.hc k (by omega)
      absorbBounds := fun h => absurd h (by omega)
      absorbFinite := fun h => absurd h (by omega)
      absorbInactive := fun h => absurd h (by omega)
      hvalid := hcert.hvalid
      hstart := hcert.hstart
      hhf := hcert.hhf
      hh := hcert.hh
      h0 := hcert.h0
      hd := hcert.hd
      hbudget := hcert.hbudget
      hmargin := fun k _ => hcert.hmargin k (by omega) }

/-- With every rate positive, the masked FloatLib clocks are the unmasked clocks. -/
lemma nrmFloatClocksM_eq_of_positive {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64)
    (hp : ∀ l j, binary64Arithmetic.lt 0 (rates l j) = true) :
    ∀ k, nrmFloatClocksM rates e marks start k = nrmFloatClocks rates e marks start k := by
  intro k
  induction k with
  | zero =>
    funext j
    simp only [nrmFloatClocksM, nrmFloatClocks, hp, ite_true]
  | succ k ih =>
    funext j
    simp only [nrmFloatClocksM, nrmFloatClocks, hp, ih, ite_true, Bool.and_true]
    by_cases hj : j = marks k
    · subst hj
      simp
    · have hne : (j.val != (marks k).val) = true := by
        simpa using Fin.val_ne_of_ne hj
      simp only [hne, ite_true, hj, ite_false]

lemma nrmFloatTimesM_eq_of_positive {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64)
    (hp : ∀ l j, binary64Arithmetic.lt 0 (rates l j) = true) (k : Nat) :
    nrmFloatTimesM rates e marks start k = nrmFloatTimes rates e marks start k := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [nrmFloatTimesM, nrmFloatTimes, nrmFloatClocksM_eq_of_positive rates e marks start hp k]

/-- With every rate positive, the masked real clocks are the unmasked real clocks. -/
lemma nrmRealClocksM_eq_of_positive {n : Nat} (rates : Nat → Fin (n + 1) → Binary64)
    (er : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1)) (start : ℝ)
    (hp : ∀ l j, 0 < floatReal (rates l j)) :
    ∀ k, nrmRealClocksM rates er marks start k = nrmRealClocks rates er marks start k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext j
    simp only [nrmRealClocksM, nrmRealClocks, updatedRealClock, ih]
    by_cases hj : j = marks k
    · simp [hj]
    · simp [hj, hp k j]

lemma nrmRealTimesM_eq_of_positive {n : Nat} (rates : Nat → Fin (n + 1) → Binary64)
    (er : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1)) (start : ℝ)
    (hp : ∀ l j, 0 < floatReal (rates l j)) (k : Nat) :
    nrmRealTimesM rates er marks start k = nrmRealTimes rates er marks start k := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [nrmRealTimesM, nrmRealTimes, nrmRealClocksM_eq_of_positive rates er marks start hp k]

lemma nrmFloatGood_subset_masked {σ : Type} {n : ℕ} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (transition : σ → Fin (n + 1) → σ) (ratesF lowerF upperF : σ → Fin (n + 1) → Binary64)
    (CF : FloatModelConsistency mf transition ratesF lowerF upperF) (initial : σ)
    (ρe : ℝ → Binary64) (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ) (fuel cap : ℕ) (save : Bool) :
    nrmFloatGood mf mr htransition transition ratesF lowerF upperF CF initial ρe start hf sr hr δ η fuel cap
        save ⊆
      nrmFloatMaskedGood mf mr htransition transition ratesF lowerF upperF CF initial ρe start hf sr hr δ η
        fuel cap save := by
  rintro ω ⟨w, hE, hcert⟩
  refine ⟨w, hE, fuel + 1, ?_⟩
  have hpos : ∀ l j, 0 < floatReal (ratesF (stateAlongWord transition initial (extendMarks w) l) j) :=
    fun l j => real_positive_of_flag _ (finite_of_valid _ (hcert.hv l j)) (hcert.hp l j)
  have hFC := nrmFloatClocksM_eq_of_positive _
    (nrmFloatExps ρe (nrmWordParse transition (fun x j => floatReal (ratesF x j)) initial w ω))
    (extendMarks w) start hcert.hp
  have hFT := nrmFloatTimesM_eq_of_positive _
    (nrmFloatExps ρe (nrmWordParse transition (fun x j => floatReal (ratesF x j)) initial w ω))
    (extendMarks w) start hcert.hp
  have hRC := nrmRealClocksM_eq_of_positive _
    (nrmRawExponentials (nrmWordParse transition (fun x j => floatReal (ratesF x j)) initial w ω))
    (extendMarks w) sr hpos
  have hRT := nrmRealTimesM_eq_of_positive _
    (nrmRawExponentials (nrmWordParse transition (fun x j => floatReal (ratesF x j)) initial w ω))
    (extendMarks w) sr hpos
  exact
    { stop := le_rfl
      hv := hcert.hv
      hi :=
        { rateValid := hcert.hi.rateValid
          startFinite := hcert.hi.startFinite
          rateNonzero := fun j _ => hcert.hi.rateNonzero j
          exponentialValid := fun j _ => hcert.hi.exponentialValid j
          quotientFinite := fun j _ => hcert.hi.quotientFinite j
          clockValid := fun j _ => hcert.hi.clockValid j
          budget := fun j _ => hcert.hi.budget j }
      hc := fun k _ hkf => by rw [hFC, hFT]; exact hcert.hc k hkf
      hcacheFinite := fun k hk j => by rw [hFC]; exact hcert.hcacheFinite k (by omega) j
      hactive := fun k _ => hpos k _
      hgap := fun k hk j hj _ => by rw [hRC]; exact hcert.hgap k (by omega) j hj
      hinc := fun k hk => by rw [hFT, hFT]; exact hcert.hinc k (by omega)
      hrinc := fun k hk => by rw [hRT, hRT]; exact hcert.hrinc k (by omega)
      hbudget := fun k hk => hcert.hbudget k (by omega)
      absorb := fun h => absurd h (by omega)
      hvalid := hcert.hvalid
      hstart := hcert.hstart
      hhf := hcert.hhf
      hh := hcert.hh
      h0 := hcert.h0
      hmargin := fun k hk => by rw [hRT]; exact hcert.hmargin k (by omega) }

end JumpProcessesLean.Proofs
