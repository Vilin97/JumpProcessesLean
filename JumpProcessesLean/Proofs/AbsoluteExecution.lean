import JumpProcessesLean.Proofs.DriverRefinement

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def absoluteCache {n : Nat} (rates c : Fin n → ℝ) (now : ℝ) : NRMState ℝ :=
  ⟨Array.ofFn rates, Array.ofFn (fun j => if 0 < rates j then some (now + c j) else none)⟩

theorem nrm_absolute_next {n : Nat} (rates c : Fin n → ℝ) (now : ℝ) (i : Fin n)
    (hi : 0 < rates i) (hmin : ∀ j, j ≠ i → 0 < rates j → c i < c j) :
    nrmNext realArithmetic (absoluteCache rates c now) = some ⟨now + c i, i.val⟩ := by
  exact nrmNext_masked_unique rates (fun j => now + c j) i hi
    (by intro j hj ha; linarith [hmin j hj ha])

lemma nrmUpdatedClock_absolute {n : Nat} (old new c u : Fin n → ℝ)
    (now : ℝ) (i j : Fin n) :
    nrmUpdatedClock (old j) (new j) (now + c j) (u j) (now + c i) j.val i.val =
      if 0 < new j then some (now + c i + maskedResidual old new i c u j) else none := by
  by_cases hn : 0 < new j
  · by_cases hji : j = i
    · subst j
      simp [nrmUpdatedClock, hn, maskedResidual, keepClock, ghostRate_of_positive hn]
    · have hv : j.val ≠ i.val := fun h => hji (Fin.ext h)
      by_cases ho : 0 < old j
      · simp only [nrmUpdatedClock, hn, ite_true, hv, ho, not_true_eq_false,
          false_or, maskedResidual, keepClock, hji, true_and]
        simp [rescaleClock, realArithmetic, hji]
      · simp [nrmUpdatedClock, hn, hv, ho, maskedResidual, keepClock, hji,
          ghostRate_of_positive hn]
  · simp [nrmUpdatedClock, hn]

/-- Exact conversion between the normalized cache used in the law proof and the
absolute clock array stored by `simulateLoop`, with the same consumed random tape. -/
theorem nrm_absolute_update_executes {n : Nat} (old new c u : Fin n → ℝ)
    (hn : ∀ j, 0 ≤ new j) (hu : ∀ j, u j ∈ Ioo 0 1) (now : ℝ) (i : Fin n)
    (hmin : ∀ j, 0 < old j → c i ≤ c j) (us es : List ℝ) :
    nrmUpdate realArithmetic (tapeSource ℝ) (absoluteCache old c now) (Array.ofFn new)
      i.val (now + c i) (List.range n).toArray
      ⟨us, nrmFreshExponentials old new u 0 i.val ++ es⟩ =
      .ok (absoluteCache new (maskedResidual old new i c u) (now + c i), ⟨us, es⟩) := by
  have hex := nrmUpdate_uniform_executes old new (fun j => now + c j) u hn hu (now + c i)
    (by intro j hj; linarith [hmin j hj]) i us es
  have hclocks : (fun j => nrmUpdatedClock (old j) (new j) (now + c j) (u j) (now + c i) j.val i.val) =
      (fun j => if 0 < new j then some (now + c i + maskedResidual old new i c u j) else none) := by
    funext j
    exact nrmUpdatedClock_absolute old new c u now i j
  rw [hclocks] at hex
  exact hex

theorem direct_real_suffix_executes (rates : Array ℝ) (hr : ∀ a ∈ rates.toList, 0 ≤ a)
    (hA : 0 < rates.toList.sum) (now e u : ℝ) (he : 0 < e)
    (hu : 0 ≤ u ∧ u < 1) (j : Nat) (hj : selection rates.toList u = some j)
    (us es : List ℝ) :
    direct realArithmetic (tapeSource ℝ) rates now ⟨u :: us, e :: es⟩ =
      .ok (some ⟨now + e / rates.toList.sum, j⟩, ⟨us, es⟩) := by
  have ht : now < now + e / rates.toList.sum := lt_add_of_pos_right _ (div_pos he hA)
  have hj' : weightedIndex realArithmetic rates (u * rates.toList.sum) = .ok j := by
    unfold weightedIndex
    change (match selection rates.toList u with | some i => Except.ok i | none => Except.error Error.selectionFailure) = _
    rw [hj]
  have hd : drawExponential realArithmetic (tapeSource ℝ) (⟨u :: us, e :: es⟩ : Tape ℝ) =
      .ok (e, ⟨u :: us, es⟩) := by
    simp [drawExponential, tapeSource, realArithmetic, Bind.bind, Except.bind, he]
    rfl
  have hu' : drawUniform realArithmetic (tapeSource ℝ) (⟨u :: us, es⟩ : Tape ℝ) =
      .ok (u, ⟨us, es⟩) := by
    simp [drawUniform, tapeSource, realArithmetic, Bind.bind, Except.bind, hu.1, hu.2]
    rfl
  unfold direct
  rw [checkRates_real rates hr]
  simp only [Bind.bind, Except.bind, sumRates_real]
  simp only [realArithmetic] at hd hu' hj' ⊢
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, hA, decide_true,
    hd, hu', Except.bind, hj', ht, Bool.true_and]
  rfl

end JumpProcessesLean.Proofs
