import JumpProcessesLean.Proofs.NRMFloatLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def nrmRealSample {n : Nat} (rates u : Fin n → ℝ) : Option (Event ℝ) :=
  match nrmInitialize realArithmetic (tapeSource ℝ) (Array.ofFn rates) 0
    ⟨[], List.ofFn (fun j => -log (u j))⟩ with
  | .ok (state, _) => nrmNext realArithmetic state
  | _ => none

noncomputable def nrmRealTime {n : Nat} (rates u : Fin n → ℝ) : ℝ :=
  ((nrmRealSample rates u).map Event.time).getD 0

noncomputable def nrmRealMark {n : Nat} (rates u : Fin n → ℝ) : Option Nat :=
  (nrmRealSample rates u).map Event.reaction

lemma nrmReal_joint_tail {n : Nat} (rates : Fin (n + 1) → ℝ)
    (hr : ∀ j, 0 < rates j) (i : Fin (n + 1)) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin (n + 1) => unitUniform))
      {u | t < nrmRealTime rates u ∧ nrmRealMark rates u = some i.val} =
      ENNReal.ofReal ((rates i / (∑ j, rates j)) * clockSurvival (∑ j, rates j) t) := by
  rw [← nrm_uniform_executable_joint_tail rates hr i t ht]
  congr 1
  ext u
  simp only [mem_setOf_eq]
  unfold nrmRealTime nrmRealMark nrmRealSample
  cases hi : nrmInitialize realArithmetic (tapeSource ℝ) (Array.ofFn rates) 0
      ⟨[], List.ofFn (fun j => -log (u j))⟩ with
  | error err => simp
  | ok p =>
    rcases p with ⟨state, rng⟩
    simp only [Except.ok.injEq, Prod.mk.injEq, exists_eq_right, exists_eq_left]
    cases hn : nrmNext realArithmetic state <;> simp [hn]

/-- Distribution approximation for the actual FloatLib initializer and minimum.
The assumptions concern input errors, finite intermediates and a race gap. No
agreement of outputs is assumed. The probability of all failures is retained. -/
theorem nrm_float_joint_tail_approx {n : Nat} (rates : Fin (n + 1) → Binary64)
    (hr : ∀ j, 0 < floatReal (rates j))
    (ef : (Fin (n + 1) → ℝ) → Fin (n + 1) → Binary64)
    (bad : Set (Fin (n + 1) → ℝ)) (hbad : MeasurableSet bad)
    (η : ℝ) (hη : 0 ≤ η)
    (hgood : ∀ u ∉ bad, (∀ j, u j ∈ Ioo 0 1) ∧
      NRMFloatCertificate rates (ef u) (fun j => -log (u j)) η ∧
      ∃ i : Fin (n + 1), ∀ j, j ≠ i →
        exponentialClock (floatReal (rates i)) (u i) + 2 * η <
          exponentialClock (floatReal (rates j)) (u j))
    (i : Fin (n + 1)) (t : ℝ) (ht : η ≤ t) :
    ENNReal.ofReal ((floatReal (rates i) / (∑ j, floatReal (rates j))) *
      clockSurvival (∑ j, floatReal (rates j)) (t + η)) ≤
      (Measure.pi (fun _ : Fin (n + 1) => unitUniform))
        {u | t < nrmFloatTime rates (ef u) ∧ nrmFloatMark rates (ef u) = some i.val} +
      (Measure.pi (fun _ : Fin (n + 1) => unitUniform)) bad ∧
    (Measure.pi (fun _ : Fin (n + 1) => unitUniform))
        {u | t < nrmFloatTime rates (ef u) ∧ nrmFloatMark rates (ef u) = some i.val} ≤
      ENNReal.ofReal ((floatReal (rates i) / (∑ j, floatReal (rates j))) *
        clockSurvival (∑ j, floatReal (rates j)) (t - η)) +
      (Measure.pi (fun _ : Fin (n + 1) => unitUniform)) bad := by
  have hg : ∀ u ∉ bad,
      |nrmFloatTime rates (ef u) - nrmRealTime (fun j => floatReal (rates j)) u| ≤ η ∧
      nrmFloatMark rates (ef u) = nrmRealMark (fun j => floatReal (rates j)) u := by
    intro u hu
    obtain ⟨hus, hc, winner, hgap⟩ := hgood u hu
    have hmin : ∀ j, j ≠ winner →
        exponentialClock (floatReal (rates winner)) (u winner) <
          exponentialClock (floatReal (rates j)) (u j) := by
      intro j hj
      linarith [hgap j hj]
    have hi := nrmInitialize_uniform_executes (fun j => floatReal (rates j)) u hr hus 0
    simp only [zero_add] at hi
    have hn := nrmNext_vector_unique (fun j => floatReal (rates j))
      (fun j => exponentialClock (floatReal (rates j)) (u j)) winner hmin
    have hf := nrm_float_certificate_refines rates (ef u) (fun j => -log (u j)) η hc
      winner hgap
    unfold nrmRealTime nrmRealMark nrmRealSample
    rw [hi]
    dsimp only
    rw [hn]
    exact hf
  have h := coupled_joint_tail_bounds
    (Measure.pi (fun _ : Fin (n + 1) => unitUniform))
    (nrmRealTime (fun j => floatReal (rates j))) (fun u => nrmFloatTime rates (ef u))
    (nrmRealMark (fun j => floatReal (rates j))) (fun u => nrmFloatMark rates (ef u))
    bad hbad η hη hg (some i.val) t
  rw [nrmReal_joint_tail _ hr i (t + η) (by linarith),
    nrmReal_joint_tail _ hr i (t - η) (by linarith)] at h
  exact h

end JumpProcessesLean.Proofs
