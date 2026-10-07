import JumpProcessesLean.Proofs.MaskedCache
import JumpProcessesLean.Proofs.FinitePathLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma marked_direct_nonnegative_law {n : Nat} (rates : Fin (n + 1) → ℝ)
    (hr : ∀ j, 0 ≤ rates j) (hA : 0 < ∑ j, rates j) (i : Fin (n + 1)) :
    directRealClockLaw (List.ofFn rates) i.val =
      ENNReal.ofReal (rates i / (∑ j, rates j)) • expMeasure (∑ j, rates j) := by
  have hd := direct_real_clock_law (List.ofFn rates)
    (by intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha; exact hr j)
    (by simpa only [List.sum_ofFn] using hA) i.val (by simpa using i.isLt)
  have hi : (List.ofFn rates)[i.val]'(by simpa using i.isLt) = rates i := by rw [List.getElem_ofFn]
  rw [hi, List.sum_ofFn] at hd
  exact hd

lemma marked_rssa_nonnegative_law {n : Nat} (rates lower upper : Fin (n + 1) → ℝ)
    (hA : 0 < ∑ j, rates j)
    (hb : ∀ j, 0 ≤ lower j ∧ lower j ≤ rates j ∧ rates j ≤ upper j) (i : Fin (n + 1)) :
    Measure.sum (fun k : Nat => rssaValidatedBranchLaw (List.ofFn rates)
      (List.ofFn lower) (List.ofFn upper) k i.val) =
      ENNReal.ofReal (rates i / (∑ j, rates j)) • expMeasure (∑ j, rates j) := by
  have hAB : (∑ j, rates j) ≤ ∑ j, upper j := Finset.sum_le_sum (fun j _ => (hb j).2.2)
  have hB : 0 < ∑ j, upper j := hA.trans_le hAB
  have hs := rssa_validated_executable_law (List.ofFn rates) (List.ofFn lower) (List.ofFn upper)
    (by simp) (by intro j hj; simpa only [List.getElem_ofFn] using hb ⟨j, by simpa using hj⟩)
    (by simpa only [List.sum_ofFn] using hA) (by simpa only [List.sum_ofFn] using hB)
    (by simpa only [List.sum_ofFn] using hAB) i.val (by simpa using i.isLt)
  have hi : (List.ofFn rates)[i.val]'(by simpa using i.isLt) = rates i := by rw [List.getElem_ofFn]
  rw [hi, List.sum_ofFn] at hs
  exact hs

theorem direct_nonnegative_word_law {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ k j, 0 ≤ rates k j) (hA : ∀ k, 0 < ∑ j, rates k j)
    (marks : Nat → Fin (n + 1)) (k : Nat) :
    directWordLaw rates marks k = targetWordLaw rates marks k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold directWordLaw independentWordLaw
    change ((directWordLaw rates marks k).prod
      (directRealClockLaw (List.ofFn (rates k)) (marks k).val)).map prependHoldingTime = _
    rw [ih, marked_direct_nonnegative_law _ (hr k) (hA k), targetWordLaw]

theorem rssa_nonnegative_word_law {n : Nat} (rates lower upper : Nat → Fin (n + 1) → ℝ)
    (hA : ∀ k, 0 < ∑ j, rates k j)
    (hb : ∀ k j, 0 ≤ lower k j ∧ lower k j ≤ rates k j ∧ rates k j ≤ upper k j)
    (marks : Nat → Fin (n + 1)) (k : Nat) :
    rssaWordLaw rates lower upper marks k = targetWordLaw rates marks k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold rssaWordLaw independentWordLaw
    change ((rssaWordLaw rates lower upper marks k).prod
      (Measure.sum (fun m : Nat => rssaValidatedBranchLaw (List.ofFn (rates k))
        (List.ofFn (lower k)) (List.ofFn (upper k)) m (marks k).val))).map prependHoldingTime = _
    rw [ih, marked_rssa_nonnegative_law _ _ _ (hA k) (hb k), targetWordLaw]

/-- Equality of all finite marked cylinder measures with inactive channels and
arbitrary activation/deactivation along a state-dependent reaction word. -/
theorem finite_masked_word_laws_equal {σ : Type} {n : Nat}
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → ℝ)
    (hr : ∀ x j, 0 ≤ rates x j) (hA : ∀ x, 0 < ∑ j, rates x j)
    (hb : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j)
    (initial : σ) (marks : Nat → Fin (n + 1)) (k : Nat) :
    let states := stateAlongWord transition initial marks
    directWordLaw (fun l => rates (states l)) marks k =
      (maskedCachedWordLaw (fun l => rates (states l)) marks k).map Prod.fst ∧
    (maskedCachedWordLaw (fun l => rates (states l)) marks k).map Prod.fst =
      rssaWordLaw (fun l => rates (states l)) (fun l => lower (states l))
        (fun l => upper (states l)) marks k := by
  dsimp only
  rw [direct_nonnegative_word_law _ (fun l => hr _) (fun l => hA _) marks k,
    masked_cached_word_marginal _ (fun l => hr _) marks k,
    rssa_nonnegative_word_law _ _ _ (fun l => hA _) (fun l => hb _) marks k]
  exact ⟨rfl, rfl⟩

end JumpProcessesLean.Proofs
