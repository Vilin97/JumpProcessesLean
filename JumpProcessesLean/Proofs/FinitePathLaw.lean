import JumpProcessesLean.Proofs.TrajectoryCache
import JumpProcessesLean.Simulation

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def independentWordLaw (clock : Nat → Measure ℝ) :
    (k : Nat) → Measure (Fin k → ℝ)
  | 0 => Measure.dirac (fun j => Fin.elim0 j)
  | k + 1 => ((independentWordLaw clock k).prod (clock k)).map prependHoldingTime

noncomputable def directWordLaw {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) : (k : Nat) → Measure (Fin k → ℝ) :=
  independentWordLaw (fun k => directRealClockLaw (List.ofFn (rates k)) (marks k).val)

noncomputable def rssaWordLaw {n : Nat} (rates lower upper : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) : (k : Nat) → Measure (Fin k → ℝ) :=
  independentWordLaw (fun k => Measure.sum (fun m : Nat =>
    rssaValidatedBranchLaw (List.ofFn (rates k)) (List.ofFn (lower k))
      (List.ofFn (upper k)) m (marks k).val))

lemma marked_direct_law {n : Nat} (rates : Fin (n + 1) → ℝ)
    (hr : ∀ j, 0 < rates j) (i : Fin (n + 1)) :
    directRealClockLaw (List.ofFn rates) i.val =
      ENNReal.ofReal (rates i / (∑ j, rates j)) • expMeasure (∑ j, rates j) := by
  have hpos : 0 < (List.ofFn rates).sum := by
    rw [List.sum_ofFn]
    exact Finset.sum_pos (fun j _ => hr j) Finset.univ_nonempty
  have hnonneg : ∀ a ∈ List.ofFn rates, 0 ≤ a := by
    intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha; exact (hr j).le
  have hd := direct_real_clock_law (List.ofFn rates) hnonneg hpos i.val (by simpa using i.isLt)
  have hi : (List.ofFn rates)[i.val]'(by simpa using i.isLt) = rates i := by
    rw [List.getElem_ofFn]
  rw [hi, List.sum_ofFn] at hd
  exact hd

theorem direct_word_law {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ k j, 0 < rates k j) (marks : Nat → Fin (n + 1)) (k : Nat) :
    directWordLaw rates marks k = targetWordLaw rates marks k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold directWordLaw independentWordLaw
    change ((directWordLaw rates marks k).prod
      (directRealClockLaw (List.ofFn (rates k)) (marks k).val)).map prependHoldingTime = _
    rw [ih, marked_direct_law _ (hr k), targetWordLaw]

theorem rssa_word_law {n : Nat} (rates lower upper : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ k j, 0 < rates k j)
    (hb : ∀ k j, 0 ≤ lower k j ∧ lower k j ≤ rates k j ∧ rates k j ≤ upper k j)
    (marks : Nat → Fin (n + 1)) (k : Nat) :
    rssaWordLaw rates lower upper marks k = targetWordLaw rates marks k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hs := operational_samplers_same_marked_time_law (rates k) (lower k) (upper k)
      (hr k) (hb k) (marks k)
    have hc : Measure.sum (fun m : Nat => rssaValidatedBranchLaw
        (List.ofFn (rates k)) (List.ofFn (lower k)) (List.ofFn (upper k)) m (marks k).val) =
        directRealClockLaw (List.ofFn (rates k)) (marks k).val := hs.2.symm.trans hs.1.symm
    unfold rssaWordLaw independentWordLaw
    change ((rssaWordLaw rates lower upper marks k).prod
      (Measure.sum (fun m : Nat => rssaValidatedBranchLaw (List.ofFn (rates k))
        (List.ofFn (lower k)) (List.ofFn (upper k)) m (marks k).val))).map prependHoldingTime = _
    rw [ih, hc, marked_direct_law _ (hr k), targetWordLaw]

def stateAlongWord {σ : Type} {n : Nat} (transition : σ → Fin (n + 1) → σ)
    (initial : σ) (marks : Nat → Fin (n + 1)) : Nat → σ
  | 0 => initial
  | k + 1 => transition (stateAlongWord transition initial marks k) (marks k)

/-- All finite reaction-word cylinder measures agree, allowing rates to depend on
the state reached by every preceding reaction. NRM's measure iterates its actual
returned cache. RSSA uses its unbounded, unnormalized first-success branch sum. -/
theorem finite_operational_word_laws_equal {σ : Type} {n : Nat}
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → ℝ)
    (hr : ∀ x j, 0 < rates x j)
    (hb : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j)
    (initial : σ) (marks : Nat → Fin (n + 1)) (k : Nat) :
    let states := stateAlongWord transition initial marks
    directWordLaw (fun l => rates (states l)) marks k =
      (nrmCachedWordLaw (fun l => rates (states l)) marks k).map Prod.fst ∧
    (nrmCachedWordLaw (fun l => rates (states l)) marks k).map Prod.fst =
      rssaWordLaw (fun l => rates (states l)) (fun l => lower (states l))
        (fun l => upper (states l)) marks k := by
  dsimp only
  rw [direct_word_law _ (fun l => hr _) marks k,
    nrm_cached_word_marginal _ (fun l => hr _) marks k,
    rssa_word_law _ _ _ (fun l => hr _) (fun l => hb _) marks k]
  exact ⟨rfl, rfl⟩

/-- Equality is preserved by every measurable trace observable, including time
censoring and recording state transitions. This statement concerns the operational
reaction-word measures; the concrete `simulateLoop` refinement is separate. -/
theorem finite_word_observables_equal {X : Type} [MeasurableSpace X] {n : Nat}
    (rates lower upper : Nat → Fin (n + 1) → ℝ) (hr : ∀ k j, 0 < rates k j)
    (hb : ∀ k j, 0 ≤ lower k j ∧ lower k j ≤ rates k j ∧ rates k j ≤ upper k j)
    (marks : Nat → Fin (n + 1)) (k : Nat) (f : (Fin k → ℝ) → X) :
    (directWordLaw rates marks k).map f =
      ((nrmCachedWordLaw rates marks k).map Prod.fst).map f ∧
    ((nrmCachedWordLaw rates marks k).map Prod.fst).map f =
      (rssaWordLaw rates lower upper marks k).map f := by
  rw [direct_word_law rates hr marks k, nrm_cached_word_marginal rates hr marks k,
    rssa_word_law rates lower upper hr hb marks k]
  exact ⟨rfl, rfl⟩

end JumpProcessesLean.Proofs
