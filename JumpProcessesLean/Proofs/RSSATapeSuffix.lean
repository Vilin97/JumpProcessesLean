import JumpProcessesLean.Proofs.RSSABranches

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

theorem rssa_first_success_suffix_executes (rates : Array ℝ) (bounds : RateBounds ℝ)
    (huppers : ∀ a ∈ bounds.upper.toList, 0 ≤ a) (hB : 0 < bounds.upper.toList.sum)
    (rejected : List ProposalInput) (last : ProposalInput) (i : Nat)
    (hg : ∀ p ∈ rejected ++ [last], GoodProposal p)
    (hr : ∀ p ∈ rejected, proposalMark rates.toList bounds.lower.toList bounds.upper.toList p.2 = none)
    (hi : proposalMark rates.toList bounds.lower.toList bounds.upper.toList last.2 = some i)
    (now elapsed : ℝ) (hz : 0 ≤ elapsed) (us es : List ℝ) (extraFuel : Nat) :
    rssaProposals realArithmetic (tapeSource ℝ) rates bounds now bounds.upper.toList.sum
      (rejected.length + 1 + extraFuel) elapsed
      ⟨proposalUniforms (rejected ++ [last]) ++ us, proposalExponentials (rejected ++ [last]) ++ es⟩ =
      .ok (some ⟨now + (elapsed + (proposalExponentials (rejected ++ [last])).sum) /
        bounds.upper.toList.sum, i⟩, ⟨us, es⟩) := by
  induction rejected generalizing elapsed with
  | nil =>
    have hg0 := hg last (by simp)
    obtain ⟨hsel, hacc⟩ := (proposalMark_some_iff _ _ _ last.2 i).mp hi
    have ha : rssaAccept realArithmetic bounds.lower[i]! rates[i]!
      (last.2.2 * bounds.upper[i]!) = true := by simpa only [Array.getElem!_toList] using hacc
    have hs := rssa_step_real rates bounds now elapsed (-log last.1) last.2.1 last.2.2 hB hz
      (neg_pos.mpr (log_neg hg0.1.1 hg0.1.2)) hg0.2.1 hg0.2.2 i extraFuel hsel us es
    simpa [proposalUniforms, proposalExponentials, ha, Nat.add_comm] using hs
  | cons p rest ih =>
    have hp := hg p (by simp)
    have hrest : ∀ q ∈ rest ++ [last], GoodProposal q := fun q hq => hg q (by simp [hq])
    have hreject := hr p (by simp)
    obtain ⟨j, hj⟩ := chooseAux_exists bounds.upper.toList huppers
      (p.2.1 * bounds.upper.toList.sum) 0 (by nlinarith [hp.2.1.1])
      (by nlinarith [hp.2.1.2]) 0
    have he : 0 < -log p.1 := neg_pos.mpr (log_neg hp.1.1 hp.1.2)
    have ha : rssaAccept realArithmetic bounds.lower[j]! rates[j]!
        (p.2.2 * bounds.upper[j]!) = false := by
      have hs : selection bounds.upper.toList p.2.1 = some j := hj
      simp only [proposalMark, proposalAcceptMark, hs, Array.getElem!_toList] at hreject
      by_cases ha : rssaAccept realArithmetic bounds.lower[j]! rates[j]!
          (p.2.2 * bounds.upper[j]!) = true
      · simp [ha] at hreject
      · exact Bool.eq_false_of_not_eq_true ha
    have hs := rssa_step_real rates bounds now elapsed (-log p.1) p.2.1 p.2.2 hB hz he
      hp.2.1 hp.2.2 j (rest.length + 1 + extraFuel) hj
      (proposalUniforms (rest ++ [last]) ++ us) (proposalExponentials (rest ++ [last]) ++ es)
    simp only [ha, Bool.false_eq_true, ite_false] at hs
    have hi' := ih hrest (fun q hq => hr q (by simp [hq])) (elapsed + -log p.1) (by linarith)
    simp only [List.cons_append, proposalUniforms, List.flatMap_cons, List.append_assoc,
      List.cons_append, List.nil_append, proposalExponentials, List.map_cons,
      List.length_cons, List.sum_cons] at hs hi' ⊢
    rw [show rest.length + 1 + 1 + extraFuel = (rest.length + 1 + extraFuel) + 1 by omega, hs]
    simpa only [add_assoc] using hi'


theorem rssa_uniform_branch_suffix_executes (rates : Array ℝ) (bounds : RateBounds ℝ)
    (huppers : ∀ a ∈ bounds.upper.toList, 0 ≤ a) (hB : 0 < bounds.upper.toList.sum)
    (k i : Nat) (u : Fin (k + 1) → ℝ) (v : Fin (k + 1) → ℝ × ℝ)
    (hu : ∀ j, u j ∈ Ioo 0 1)
    (hv : ∀ j, (v j).1 ∈ Ioo 0 1 ∧ (v j).2 ∈ Ioo 0 1)
    (hbranch : v ∈ proposalBranch rates.toList bounds.lower.toList bounds.upper.toList k i)
    (now : ℝ) (us es : List ℝ) (extraFuel : Nat) :
    rssaProposals realArithmetic (tapeSource ℝ) rates bounds now bounds.upper.toList.sum (k + 1 + extraFuel) 0
      ⟨proposalUniforms (List.ofFn (fun j => (u j, v j))) ++ us,
        proposalExponentials (List.ofFn (fun j => (u j, v j))) ++ es⟩ =
      .ok (some ⟨now + ∑ j, exponentialClock bounds.upper.toList.sum (u j), i⟩, ⟨us, es⟩) := by
  let samples : Fin (k + 1) → ProposalInput := fun j => (u j, v j)
  let rejected : List ProposalInput := List.ofFn (fun j : Fin k => samples j.castSucc)
  have hlist : rejected ++ [samples (Fin.last k)] = List.ofFn samples :=
    List.ofFn_succ_last.symm
  have hgood : ∀ p ∈ rejected ++ [samples (Fin.last k)], GoodProposal p := by
    rw [hlist]
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨hu j, hv j⟩
  have hrejected : ∀ p ∈ rejected,
      proposalMark rates.toList bounds.lower.toList bounds.upper.toList p.2 = none := by
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    have h := (mem_pi.mp hbranch) j.castSucc (mem_univ _)
    simpa [Fin.isLt] using h
  have hlast : proposalMark rates.toList bounds.lower.toList bounds.upper.toList
      (samples (Fin.last k)).2 = some i := by
    have h := (mem_pi.mp hbranch) (Fin.last k) (mem_univ _)
    simpa using h
  have hex := rssa_first_success_suffix_executes rates bounds huppers hB rejected (samples (Fin.last k))
    i hgood hrejected hlast now 0 (le_refl 0) us es extraFuel
  rw [hlist] at hex
  simp only [rejected, List.length_ofFn, zero_add] at hex
  have hsum : (proposalExponentials (List.ofFn samples)).sum / bounds.upper.toList.sum =
      ∑ j, exponentialClock bounds.upper.toList.sum (u j) := by
    simp only [proposalExponentials, List.map_ofFn, Function.comp_def, List.sum_ofFn, samples,
      exponentialClock, Finset.sum_div]
  simpa only [hsum] using hex


end JumpProcessesLean.Proofs
