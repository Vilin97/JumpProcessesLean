import JumpProcessesLean.Proofs.FloatSchedule

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

def floatPacketTape {γ : Type} (u e : Nat → γ → List Binary64) (source : Nat → γ) : Nat → Nat → Tape Binary64
  | _, 0 => ⟨[], []⟩
  | k, count + 1 =>
    let rest := floatPacketTape u e source (k + 1) count
    ⟨u k (source k) ++ rest.uniforms, e k (source k) ++ rest.exponentials⟩

noncomputable def floatTimeSchedule {γ : Type} (clock : Nat → Binary64 → γ → Binary64)
    (source : Nat → γ) (start : Binary64) : Nat → Binary64
  | 0 => start
  | k + 1 => clock k (floatTimeSchedule clock source start k) (source k)

noncomputable def realTimeSchedule {γ : Type} (clock : Nat → γ → ℝ)
    (source : Nat → γ) (start : ℝ) : Nat → ℝ
  | 0 => start
  | k + 1 => realTimeSchedule clock source start k + clock k (source k)

/-- Local primitive packet refinement, before any simulation driver is run. -/
structure LocalPacketRefinement {σ γ : Type} (model : Model Binary64 σ) (algorithm : Algorithm)
    (states : Nat → σ) (marks : Nat → Nat) (clock : Nat → Binary64 → γ → Binary64)
    (u e : Nat → γ → List Binary64) (realClock : Nat → γ → ℝ)
    (source : Nat → γ) (start : Binary64) (cap limit : Nat) (d : ℝ) : Prop where
  execute : ∀ k, k ≤ limit → ∀ us es,
    sampleEvent binary64Arithmetic (tapeSource Binary64) model algorithm cap (states k)
      (floatTimeSchedule clock source start k)
      ⟨u k (source k) ++ us, e k (source k) ++ es⟩ none =
        .ok (some ⟨floatTimeSchedule clock source start (k + 1), marks k⟩, ⟨us, es⟩)
  finite : ∀ k, k ≤ limit → ExecFloat.Binary.isFinite (floatTimeSchedule clock source start (k + 1)) = true
  increasing : ∀ k, k ≤ limit → binary64Arithmetic.le (floatTimeSchedule clock source start k)
    (floatTimeSchedule clock source start (k + 1)) = true
  positive : ∀ k, k ≤ limit → 0 ≤ realClock k (source k)
  error : ∀ k, k ≤ limit → |floatReal (floatTimeSchedule clock source start (k + 1)) -
    (floatReal (floatTimeSchedule clock source start k) + realClock k (source k))| ≤ d

/-- The local bounds are propagated by induction; no accumulated output-error
hypothesis is required. -/
theorem packet_accumulated_time_error {σ γ : Type} (model : Model Binary64 σ) (algorithm : Algorithm)
    (states : Nat → σ) (marks : Nat → Nat) (clock : Nat → Binary64 → γ → Binary64)
    (u e : Nat → γ → List Binary64) (realClock : Nat → γ → ℝ)
    (source : Nat → γ) (start : Binary64) (sr : ℝ) (cap limit : Nat) (d ε : ℝ)
    (P : LocalPacketRefinement model algorithm states marks clock u e realClock source start cap limit d)
    (hstart : |floatReal start - sr| ≤ ε) (k : Nat) (hk : k ≤ limit + 1) :
    |floatReal (floatTimeSchedule clock source start k) - realTimeSchedule realClock source sr k| ≤
      ε + (k : ℝ) * d := by
  induction k with
  | zero => simpa only [floatTimeSchedule, realTimeSchedule, Nat.cast_zero, zero_mul, add_zero] using hstart
  | succ k ih =>
    have h := absolute_time_error _ _ _ _ (ε + (k : ℝ) * d) d (ih (by omega)) (P.error k (by omega))
    simpa only [realTimeSchedule, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using h

/-- Whole native Direct/RSSA float simulation composition. Public instances below
construct `P` by the proved numerical input certificates. -/
theorem float_packet_trajectory_close {σ γ : Type} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (algorithm : Algorithm) (hnrm : algorithm ≠ .nrm)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Nat)
    (clock : Nat → Binary64 → γ → Binary64) (u e : Nat → γ → List Binary64)
    (realClock : Nat → γ → ℝ) (source : Nat → γ)
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
        (floatPacketTape u e source 0 (fuel + 1)) fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (realTimeSchedule realClock source sr) marks 0 (fuel + 1))) := by
  let tf := floatTimeSchedule clock source start
  let tr := realTimeSchedule realClock source sr
  let tape := floatPacketTape u e source
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
    change sampleEvent _ _ _ _ _ _ _ (floatPacketTape u e source k (count + 1)) _ = _
    rw [floatPacketTape]
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

end JumpProcessesLean.Proofs
