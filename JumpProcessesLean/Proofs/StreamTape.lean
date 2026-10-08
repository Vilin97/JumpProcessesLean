import JumpProcessesLean.Proofs.IIDStreams
import JumpProcessesLean.Proofs.EndToEnd

/-!
# Random tapes read from IID streams

`streamTape a b ω` is the public `tapeSource` tape filled with the first `a` uniforms
and the first `b` exponentials `-log V_i` of the IID streams. This file connects
sequentially read primitive blocks to the actual public driver for arbitrary unread
tape suffixes, and assembles reaction-word branches of the IID streams.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- The finite random tape read from the IID streams. -/
noncomputable def streamTape (a b : ℕ) (ω : Streams) : Tape ℝ :=
  ⟨List.ofFn (fun i : Fin a => ω (.inl i)), List.ofFn (fun i : Fin b => -log (ω (.inr i)))⟩

lemma streamTape_split (a b c d : ℕ) (ω : Streams) :
    streamTape (a + c) (b + d) ω =
      ⟨List.ofFn (fun i : Fin a => ω (.inl i)) ++ (streamTape c d (streamsDrop a b ω)).uniforms,
        List.ofFn (fun i : Fin b => -log (ω (.inr i))) ++
          (streamTape c d (streamsDrop a b ω)).exponentials⟩ := by
  simp only [streamTape, List.ofFn_add, streamsDrop, Sum.map_inl, Sum.map_inr]
  rfl

/-- Packet tapes followed by an arbitrary unread tape. -/
def packetTapeFrom {γ : Type} (uniforms exponentials : Nat → γ → List ℝ)
    (source : Nat → γ) (tail : Tape ℝ) : Nat → Nat → Tape ℝ
  | _, 0 => tail
  | k, count + 1 =>
    let next := packetTapeFrom uniforms exponentials source tail (k + 1) count
    ⟨uniforms k (source k) ++ next.uniforms, exponentials k (source k) ++ next.exponentials⟩

theorem packet_schedule_concrete_run_from {σ γ : Type} {n : Nat} (model : Model ℝ σ)
    (algorithm : Algorithm) (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1))
    (P : PacketSpecification (γ := γ) model algorithm states rates marks)
    (source : Nat → γ) (tail : Tape ℝ) (start : ℝ) (limit cap : Nat)
    (hg : ∀ k, k ≤ limit → P.good k (source k))
    (hcost : ∀ k, k ≤ limit → P.cost k (source k) ≤ cap)
    (hs : ∀ k, model.transition (states k) (marks k).val = .ok (states (k + 1)))
    (k fuel : Nat) (hlen : k + fuel ≤ limit) :
    let c := fun l (_ : Fin (n + 1)) => P.clock l (source l)
    let times := nrmScheduleTime c marks start
    ConcreteRun realArithmetic (tapeSource ℝ) model algorithm cap fuel (states k) (times k)
      (packetTapeFrom P.uniforms P.exponentials source tail k (fuel + 1)) none
      (nrmScheduleEvents rates c marks times k fuel) := by
  dsimp only
  let c := fun l (_ : Fin (n + 1)) => P.clock l (source l)
  let times := nrmScheduleTime c marks start
  induction fuel generalizing k with
  | zero =>
    rw [nrmScheduleEvents]
    by_cases hA : 0 < ∑ j, rates k j
    · rw [if_pos hA]
      apply ConcreteRun.budget
      rw [packetTapeFrom]
      exact P.execute k (source k) (hg k (by omega)) hA cap (hcost k (by omega)) (times k) _ _
    · rw [if_neg hA]
      apply ConcreteRun.absorb
      exact P.absorb k hA cap (times k) _
  | succ fuel ih =>
    rw [nrmScheduleEvents]
    by_cases hA : 0 < ∑ j, rates k j
    · rw [if_pos hA]
      apply ConcreteRun.next
        (newState := states (k + 1)) (newCache := none)
        (newRng := packetTapeFrom P.uniforms P.exponentials source tail (k + 1) (fuel + 1))
      · rw [packetTapeFrom]
        exact P.execute k (source k) (hg k (by omega)) hA cap (hcost k (by omega)) (times k) _ _
      · exact hs k
      · cases algorithm <;> try rfl
      · exact ih (k + 1) (by omega)
    · rw [if_neg hA]
      apply ConcreteRun.absorb
      exact P.absorb k hA cap (times k) _

lemma rawWordGood_of_index {γ : Type} (good : Nat → γ → Prop) {k : Nat} (p : Fin k → γ)
    (h : ∀ q : Fin k, good (k - 1 - q.val) (p q)) : RawWordGood good k p := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine ⟨ih (Fin.tail p) (fun q => ?_), ?_⟩
    · have hq := h q.succ
      have he : k + 1 - 1 - q.succ.val = k - 1 - q.val := by simp only [Fin.val_succ]; omega
      simpa only [he, Fin.tail] using hq
    · simpa using h 0

/-- Pointwise driver refinement for primitive packets followed by any unread tape.
Only the packet costs actually reached by the transcript are bounded by the cap. -/
theorem packet_driver_executes_from {σ γ : Type} {n : Nat}
    (model : Model ℝ σ) (algorithm : Algorithm)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (P : PacketSpecification (γ := γ) model algorithm states rates marks)
    (fallback : γ) (hs : ∀ k, model.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start horizon : ℝ) (hstart : start < horizon) (fuel cap : Nat) (saveEvents : Bool)
    (p : Fin (fuel + 1) → γ) (hp : RawWordGood P.good (fuel + 1) p)
    (hcost : ∀ k, k ≤ fuel → P.cost k (rawChronological fallback p k) ≤ cap) (tail : Tape ℝ) :
    observeRun (simulate realArithmetic (tapeSource ℝ) model algorithm (states 0) start horizon
      (packetTapeFrom P.uniforms P.exponentials (rawChronological fallback p) tail 0 (fuel + 1))
      fuel saveEvents cap) =
    holdingSimulationObservation model states rates marks start horizon fuel saveEvents
      (rawWordHoldings P.clock (fuel + 1) p) := by
  let source := rawChronological fallback p
  let c := fun l (_ : Fin (n + 1)) => P.clock l (source l)
  let times := nrmScheduleTime c marks start
  have hrun := packet_schedule_concrete_run_from model algorithm states rates marks P source tail start
    fuel cap (fun k hk => raw_chronological_good fallback p P.good hp k (by omega)) hcost hs 0 fuel
    (by omega)
  have he := simulate_refines_replay (tapeSource ℝ) model algorithm (states 0) start horizon hstart
    (packetTapeFrom P.uniforms P.exponentials source tail 0 (fuel + 1))
    (packetTapeFrom P.uniforms P.exponentials source tail 0 (fuel + 1)) none fuel cap saveEvents _
    (by cases algorithm with
        | direct => rfl
        | rssa => rfl
        | nrm => exact (P.uncached rfl).elim) hrun
  rw [he]
  unfold holdingSimulationObservation
  have htimes : ∀ l, l ≤ fuel + 1 →
      times l = nrmScheduleTime (holdingSchedule (rawWordHoldings P.clock (fuel + 1) p)) marks start l := by
    intro l hl
    induction l with
    | zero => rfl
    | succ l ih =>
      change times l + P.clock l (source l) = _
      rw [nrmScheduleTime, ih (by omega), raw_chronological_clock fallback p P.clock l (by omega) (marks l)]
  rw [schedule_events_times_congr rates c _ marks _ _ (fuel + 1) htimes 0 fuel (by omega)]

/-- Disjoint reaction-word events of total probability one decompose the law of any
function that agrees almost surely on each event with a measurable branch formula. -/
theorem iid_word_decomposition {X ι : Type} [MeasurableSpace X] [Fintype ι]
    (E : ι → Set Streams) (hE : ∀ w, MeasurableSet (E w))
    (hd : Pairwise (Function.onFun Disjoint E)) (hmass : ∑ w, iidStreams (E w) = 1)
    (F : Streams → X) (G : ι → Streams → X) (hG : ∀ w, Measurable (G w))
    (hFG : ∀ w, ∀ᵐ ω ∂iidStreams, ω ∈ E w → F ω = G w ω) :
    iidStreams.map F = Measure.sum (fun w => (iidStreams.restrict (E w)).map (G w)) := by
  have hae : ∀ w, F =ᵐ[iidStreams.restrict (E w)] G w := fun w =>
    (ae_restrict_iff' (hE w)).mpr (hFG w)
  rw [map_eq_sum_restrict_of_partition iidStreams E hE hd (by rw [tsum_fintype, hmass, measure_univ]) F
    (fun w => (hG w).aemeasurable.congr (hae w).symm)]
  congr 1
  funext w
  exact Measure.map_congr (hae w)

/-- States reached along two reaction words agree up to their first difference. -/
lemma stateAlongWord_congr {σ : Type} {n : Nat} (transition : σ → Fin (n + 1) → σ)
    (initial : σ) (m m' : Nat → Fin (n + 1)) (l : Nat) (h : ∀ j, j < l → m j = m' j) :
    stateAlongWord transition initial m l = stateAlongWord transition initial m' l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    simp only [stateAlongWord]
    rw [ih (fun j hj => h j (by omega)), h l (by omega)]

/-- Distinct words are separated by a sequential deterministic choice. -/
lemma words_eq_of_sequential_choice {n K : Nat} (w w' : Fin K → Fin (n + 1))
    (h : ∀ l (hl : l < K), (∀ j (hj : j < l), w ⟨j, by omega⟩ = w' ⟨j, by omega⟩) →
      w ⟨l, hl⟩ = w' ⟨l, hl⟩) : w = w' := by
  have hall : ∀ l (hl : l < K), w ⟨l, hl⟩ = w' ⟨l, hl⟩ := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih => exact fun hl => h l hl (fun j hj => ih j hj (by omega))
  funext q
  exact hall q.val q.isLt

lemma extendMarks_agree {n K : Nat} (w w' : Fin K → Fin (n + 1)) (l : Nat)
    (h : ∀ j (hj : j < l) (hjK : j < K), w ⟨j, hjK⟩ = w' ⟨j, hjK⟩) :
    ∀ j, j < l → extendMarks w j = extendMarks w' j := by
  intro j hj
  unfold extendMarks
  by_cases hjK : j < K
  · simp only [hjK, dite_true]
    exact h j hj hjK
  · simp only [hjK, dite_false]

lemma iidStreams_ae_mem_Ioo : ∀ᵐ ω ∂iidStreams, ∀ x, ω x ∈ Ioo (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro x
  have h := (measurePreserving_eval_infinitePi (fun _ : ℕ ⊕ ℕ => unitUniform) x).quasiMeasurePreserving
  exact h.tendsto_ae.eventually unitUniform_ae_mem

end JumpProcessesLean.Proofs
