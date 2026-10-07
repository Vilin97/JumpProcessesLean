import JumpProcessesLean.Proofs.NRMRawSupport

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def nrmRawPrefix {n k : Nat} (p : NRMRawInput n k) (l : Nat) (hl : l ≤ k) : NRMRawInput n l :=
  (p.1, fun q => p.2 ⟨k - l + q.val, by omega⟩)

noncomputable def nrmRawFresh {n k : Nat} (p : NRMRawInput n k) (l : Nat) : Fin (n + 1) → ℝ :=
  if h : l < k then p.2 ⟨k - 1 - l, by omega⟩ else fun _ => 1 / 2

lemma nrmRawPrefix_self {n k : Nat} (p : NRMRawInput n k) :
    nrmRawPrefix p k (le_refl k) = p := by
  apply Prod.ext
  · rfl
  funext q
  simp [nrmRawPrefix]

lemma nrmRawPrefix_step {n k : Nat} (p : NRMRawInput n k) (l : Nat) (hl : l + 1 ≤ k) :
    ((nrmRawPrefix p (l + 1) hl).1, Fin.tail (nrmRawPrefix p (l + 1) hl).2) =
      nrmRawPrefix p l (by omega) := by
  apply Prod.ext
  · rfl
  funext q
  unfold nrmRawPrefix Fin.tail
  dsimp only
  apply congrArg p.2
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

lemma nrmRawPrefix_fresh {n k : Nat} (p : NRMRawInput n k) (l : Nat) (hl : l + 1 ≤ k) :
    (nrmRawPrefix p (l + 1) hl).2 0 = nrmRawFresh p l := by
  unfold nrmRawPrefix nrmRawFresh
  rw [dif_pos (by omega)]
  dsimp only
  apply congrArg p.2
  apply Fin.ext
  simp only [Fin.val_zero, add_zero]
  omega

lemma nrmRawPrefix_tail {n k : Nat} (p : NRMRawInput n (k + 1)) (l : Nat) (hl : l ≤ k) :
    nrmRawPrefix (p.1, Fin.tail p.2) l hl = nrmRawPrefix p l (by omega) := by
  apply Prod.ext
  · rfl
  funext q
  unfold nrmRawPrefix Fin.tail
  dsimp only
  apply congrArg p.2
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

lemma nrm_raw_prefix_good {n k : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (p : NRMRawInput n k) (hg : NRMRawGood rates marks k p)
    (l : Nat) (hl : l ≤ k) : NRMRawGood rates marks l (nrmRawPrefix p l hl) := by
  induction k with
  | zero =>
    have h : l = 0 := by omega
    subst l
    simpa [nrmRawPrefix_self] using hg
  | succ k ih =>
    by_cases he : l = k + 1
    · subst l
      simpa [nrmRawPrefix_self] using hg
    · have hlk : l ≤ k := by omega
      have hi := ih (p.1, Fin.tail p.2) hg.1 hlk
      simpa only [nrmRawPrefix_tail] using hi

lemma nrm_raw_prefix_cache {n k : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (p : NRMRawInput n k) (l : Nat) (hl : l ≤ k) :
    (nrmRawHistory rates marks l (nrmRawPrefix p l hl)).2 =
      nrmScheduleCache rates marks p.1 (nrmRawFresh p) l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [nrmRawHistory]
    dsimp only
    rw [nrmRawPrefix_step, nrmRawPrefix_fresh, ih (by omega)]
    rfl

theorem nrm_raw_schedule_uniforms {n k : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (p : NRMRawInput n k) (hg : NRMRawGood rates marks k p) :
    (∀ j, p.1 j ∈ Ioo 0 1) ∧ (∀ l j, nrmRawFresh p l j ∈ Ioo 0 1) := by
  have hi := nrm_raw_prefix_good rates marks p hg 0 (by omega)
  refine ⟨hi, ?_⟩
  intro l j
  by_cases hl : l < k
  · have hp := nrm_raw_prefix_good rates marks p hg (l + 1) (by omega)
    rw [NRMRawGood, nrmRawPrefix_fresh] at hp
    exact hp.2.1 j
  · simp [nrmRawFresh, hl]
    norm_num

theorem nrm_raw_schedule_winners {n k : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (p : NRMRawInput n k) (hg : NRMRawGood rates marks k p) :
    ∀ l, l < k →
      0 < rates l (marks l) ∧ 0 < nrmScheduleCache rates marks p.1 (nrmRawFresh p) l (marks l) ∧
      ∀ j, j ≠ marks l → 0 < rates l j →
        nrmScheduleCache rates marks p.1 (nrmRawFresh p) l (marks l) <
          nrmScheduleCache rates marks p.1 (nrmRawFresh p) l j := by
  intro l hl
  have hp := nrm_raw_prefix_good rates marks p hg (l + 1) (by omega)
  have hb := hp.2.2
  rw [nrmRawPrefix_step, nrm_raw_prefix_cache] at hb
  exact hb

/-- The public simulator executes an actual compiled primitive tape almost
everywhere on each NRM word branch. There is no output equality in the premises. -/
theorem nrm_raw_driver_executes {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (hr : ∀ l j, 0 ≤ rates l j)
    (hm : ∀ l, model.rates (states l) = Array.ofFn (rates l))
    (hs : ∀ l, model.transition (states l) (marks l).val = .ok (states (l + 1)))
    (start horizon : ℝ) (hstart : start < horizon) (fuel maxProposals : Nat) (saveEvents : Bool) :
    ∀ᵐ p ∂nrmRawPathLaw rates marks (fuel + 1),
      let c := nrmScheduleCache rates marks p.1 (nrmRawFresh p)
      let times := nrmScheduleTime c marks start
      observeRun (simulate realArithmetic (tapeSource ℝ) model .nrm (states 0) start horizon
        ⟨[], nrmFreshExponentials (fun _ => 0) (rates 0) p.1 0 0 ++
          nrmScheduleTape rates marks (nrmRawFresh p) 0 fuel⟩ fuel saveEvents maxProposals) =
      replayEvents realArithmetic model horizon saveEvents fuel (states 0) start 0 #[(start, states 0)]
        (nrmScheduleEvents rates c marks times 0 fuel) := by
  filter_upwards [nrm_raw_good_ae rates marks (fuel + 1)] with p hp
  obtain ⟨hi, hu⟩ := nrm_raw_schedule_uniforms rates marks p hp
  apply nrm_simulate_primitive_execution model states rates marks p.1 (nrmRawFresh p) start horizon
    hstart hr hi hu hm hs fuel maxProposals
  intro l hl hA
  exact nrm_raw_schedule_winners rates marks p hp l (by omega)

end JumpProcessesLean.Proofs
