import JumpProcessesLean.Proofs.DirectFloatLaw
import JumpProcessesLean.Proofs.RSSABranches

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

def uniformFlag (u : Binary64) : Bool :=
  binary64Arithmetic.finite u && binary64Arithmetic.le 0 u && binary64Arithmetic.lt u 1

def exponentialFlag (e : Binary64) : Bool :=
  binary64Arithmetic.finite e && binary64Arithmetic.lt 0 e

def clockFlag (now elapsed total : Binary64) : Bool :=
  binary64Arithmetic.finite (now + elapsed / total) && binary64Arithmetic.lt now (now + elapsed / total)

def floatProposalMark (rates : Array Binary64) (bounds : RateBounds Binary64)
    (total u v : Binary64) : Option Nat :=
  match chooseAux binary64Arithmetic (u * total) bounds.upper.toList 0 0 with
  | none => none
  | some j => if rssaAccept binary64Arithmetic bounds.lower[j]! rates[j]!
      (v * bounds.upper[j]!) then some j else none

/-- Numerical input certificate for one proposal. CDF and acceptance margins
derive the branching decisions; no output agreement is part of the certificate. -/
structure RSSAProposalCertificate (rates : Array Binary64) (bounds : RateBounds Binary64)
    (total u v : Binary64) (ur vr η : ℝ) : Prop where
  upperFold : FoldFinite 0 bounds.upper.toList
  thresholdFinite : ExecFloat.Binary.isFinite (u * total) = true
  thresholdError : |floatReal (u * total) - ur * (bounds.upper.toList.map floatReal).sum| ≤ η
  prefixBudget : ∀ j : Nat, j < bounds.upper.size → foldRoundBudget 0 (bounds.upper.toList.take (j + 1)) ≤ η
  cdfMargin : ∀ j : Nat, j < bounds.upper.size →
    2 * η < |ur * (bounds.upper.toList.map floatReal).sum - ((bounds.upper.toList.take (j + 1)).map floatReal).sum|
  shape : bounds.lower.size = rates.size ∧ bounds.upper.size = rates.size
  finiteRates : ∀ j : Nat, j < rates.size → ExecFloat.Binary.isFinite rates[j]! = true
  finiteLower : ∀ j : Nat, j < rates.size → ExecFloat.Binary.isFinite bounds.lower[j]! = true
  lowerEncloses : ∀ j : Nat, j < rates.size → floatReal bounds.lower[j]! ≤ floatReal rates[j]!
  acceptanceFinite : ∀ j : Nat, j < rates.size → ExecFloat.Binary.isFinite (v * bounds.upper[j]!) = true
  acceptanceError : ∀ j : Nat, j < rates.size →
    |floatReal (v * bounds.upper[j]!) - vr * floatReal bounds.upper[j]!| ≤ η
  acceptanceMargin : ∀ j : Nat, j < rates.size → 0 < floatReal rates[j]! →
    2 * η < |vr * floatReal bounds.upper[j]! - floatReal rates[j]!|

theorem rssa_proposal_certificate_refines (rates : Array Binary64) (bounds : RateBounds Binary64)
    (total u v : Binary64) (ur vr η : ℝ) (hc : RSSAProposalCertificate rates bounds total u v ur vr η)
    (huppers : ∀ a ∈ bounds.upper.toList.map floatReal, 0 ≤ a)
    (hB : 0 < (bounds.upper.toList.map floatReal).sum) (hu : ur ∈ Ioo 0 1) :
    floatProposalMark rates bounds total u v = proposalMark (rates.toList.map floatReal)
      (bounds.lower.toList.map floatReal) (bounds.upper.toList.map floatReal) (ur, vr) := by
  obtain ⟨j, hj⟩ := chooseAux_exists (bounds.upper.toList.map floatReal) huppers
    (ur * (bounds.upper.toList.map floatReal).sum) 0 (by nlinarith [hu.1]) (by nlinarith [hu.2]) 0
  have hsel := chooseAux_float_margin bounds.upper.toList 0 (u * total)
    (ur * (bounds.upper.toList.map floatReal).sum) η hc.upperFold hc.thresholdFinite hc.thresholdError
    (by intro k hk; exact hc.prefixBudget k (by simpa using hk))
    (by intro k hk; simpa only [floatReal_zero, zero_add] using hc.cdfMargin k (by simpa using hk)) 0
  simp only [floatReal_zero] at hsel
  rw [hj] at hsel
  have hbound : j < rates.size := by
    have hx := (chooseAux_some_bounds _ _ _ _ _ hj).2
    simpa [hc.shape.2] using hx
  have haccept : rssaAccept binary64Arithmetic bounds.lower[j]! rates[j]! (v * bounds.upper[j]!) =
      rssaAccept realArithmetic (floatReal bounds.lower[j]!) (floatReal rates[j]!)
        (vr * floatReal bounds.upper[j]!) := by
    rw [rssa_float_accept_decode _ _ _ (hc.finiteLower j hbound) (hc.finiteRates j hbound)
      (hc.acceptanceFinite j hbound) (hc.lowerEncloses j hbound),
      rssa_lower_shortcut _ _ _ (hc.lowerEncloses j hbound)]
    by_cases ha : 0 < floatReal rates[j]!
    · simp only [ha, true_and]
      apply decide_eq_decide.mpr
      exact rejection_margin_stable (vr * floatReal bounds.upper[j]!) (floatReal rates[j]!)
        (floatReal (v * bounds.upper[j]!)) (floatReal rates[j]!) η
        (hc.acceptanceError j hbound) (by simp only [sub_self, abs_zero]; exact (abs_nonneg _).trans hc.thresholdError)
        (hc.acceptanceMargin j hbound ha)
    · simp [ha]
  have hget (xs : Array Binary64) (h : j < xs.size) :
      (xs.toList.map floatReal)[j]! = floatReal xs[j]! := by
    have hl : j < (xs.toList.map floatReal).length := by
      simpa only [List.length_map, Array.length_toList] using h
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    simp [h]
  unfold floatProposalMark proposalMark proposalAcceptMark
  rw [hsel]
  change (if rssaAccept binary64Arithmetic _ _ _ then some j else none) =
    (match selection (bounds.upper.toList.map floatReal) ur with
      | none => none
      | some k => if rssaAccept realArithmetic (bounds.lower.toList.map floatReal)[k]!
          (rates.toList.map floatReal)[k]! (vr * (bounds.upper.toList.map floatReal)[k]!) then some k else none)
  have hj' : selection (bounds.upper.toList.map floatReal) ur = some j := hj
  rw [hj']
  dsimp only
  rw [hget bounds.lower (by simpa [hc.shape.1] using hbound), hget rates hbound,
    hget bounds.upper (by simpa [hc.shape.2] using hbound), haccept]

lemma rssa_step_float_flags (rates : Array Binary64) (bounds : RateBounds Binary64)
    (now total elapsed e u v : Binary64) (j fuel : Nat)
    (hu : uniformFlag u = true) (hv : uniformFlag v = true) (he : exponentialFlag e = true)
    (hel : binary64Arithmetic.finite (elapsed + e) = true)
    (hj : chooseAux binary64Arithmetic (u * total) bounds.upper.toList 0 0 = some j)
    (ht : rssaAccept binary64Arithmetic bounds.lower[j]! rates[j]! (v * bounds.upper[j]!) = true →
      clockFlag now (elapsed + e) total = true) (us es : List Binary64) :
    rssaProposals binary64Arithmetic (tapeSource Binary64) rates bounds now total (fuel + 1)
      elapsed ⟨u :: v :: us, e :: es⟩ =
    if rssaAccept binary64Arithmetic bounds.lower[j]! rates[j]! (v * bounds.upper[j]!) then
      .ok (some ⟨now + (elapsed + e) / total, j⟩, ⟨us, es⟩)
    else rssaProposals binary64Arithmetic (tapeSource Binary64) rates bounds now total
      fuel (elapsed + e) ⟨us, es⟩ := by
  have hdU : drawUniform binary64Arithmetic (tapeSource Binary64)
      (⟨u :: v :: us, e :: es⟩ : Tape Binary64) = .ok (u, ⟨v :: us, e :: es⟩) := by
    simp only [drawUniform, tapeSource, Bind.bind, Except.bind]
    rw [show (binary64Arithmetic.finite u && binary64Arithmetic.le binary64Arithmetic.zero u &&
      binary64Arithmetic.lt u binary64Arithmetic.one) = true from hu]
    rfl
  have hdE : drawExponential binary64Arithmetic (tapeSource Binary64)
      (⟨v :: us, e :: es⟩ : Tape Binary64) = .ok (e, ⟨v :: us, es⟩) := by
    simp only [drawExponential, tapeSource, Bind.bind, Except.bind]
    rw [show (binary64Arithmetic.finite e && binary64Arithmetic.lt binary64Arithmetic.zero e) = true from he]
    rfl
  have hdV : drawUniform binary64Arithmetic (tapeSource Binary64)
      (⟨v :: us, es⟩ : Tape Binary64) = .ok (v, ⟨us, es⟩) := by
    simp only [drawUniform, tapeSource, Bind.bind, Except.bind]
    rw [show (binary64Arithmetic.finite v && binary64Arithmetic.le binary64Arithmetic.zero v &&
      binary64Arithmetic.lt v binary64Arithmetic.one) = true from hv]
    rfl
  have hs : weightedIndex binary64Arithmetic bounds.upper (binary64Arithmetic.mul u total) = .ok j := by
    unfold weightedIndex
    change (match chooseAux binary64Arithmetic (u * total) bounds.upper.toList 0 0 with
      | some k => Except.ok k | none => Except.error Error.selectionFailure) = Except.ok j
    rw [hj]
  rw [rssaProposals, hdU]
  simp only [Bind.bind, Except.bind]
  rw [hs]
  simp only [Except.bind]
  rw [hdE]
  simp only [Except.bind]
  rw [show binary64Arithmetic.add elapsed e = elapsed + e from rfl, hel]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hdV]
  simp only [Except.bind]
  by_cases ha : rssaAccept binary64Arithmetic bounds.lower[j]! rates[j]! (v * bounds.upper[j]!) = true
  · have hc : (binary64Arithmetic.finite (binary64Arithmetic.add now (binary64Arithmetic.div (elapsed + e) total)) &&
      binary64Arithmetic.lt now (binary64Arithmetic.add now (binary64Arithmetic.div (elapsed + e) total))) = true := ht ha
    simp only [show rssaAccept binary64Arithmetic bounds.lower[j]! rates[j]!
      (binary64Arithmetic.mul v bounds.upper[j]!) = true from ha, ha, hc,
      Bool.not_true, Bool.false_eq_true, ite_false, ite_true, Pure.pure, Except.pure]
    rfl
  · simp only [show rssaAccept binary64Arithmetic bounds.lower[j]! rates[j]!
      (binary64Arithmetic.mul v bounds.upper[j]!) = false from Bool.eq_false_of_not_eq_true ha,
      ha, Bool.false_eq_true, ite_false]

def proposalFloatUniforms {k : Nat} (u v : Fin k → Binary64) : List Binary64 :=
  (List.ofFn (fun j => (u j, v j))).flatMap (fun p => [p.1, p.2])

/-- Every rejected proposal contributes its rounded exponential to the same running
sum. The accepted event consumes precisely the stated proposal tape. -/
theorem rssa_float_branch_executes {k : Nat} (rates : Array Binary64) (bounds : RateBounds Binary64)
    (now total elapsed : Binary64) (e u v : Fin (k + 1) → Binary64) (j : Fin (k + 1) → Nat)
    (hu : ∀ q, uniformFlag (u q) = true) (hv : ∀ q, uniformFlag (v q) = true)
    (he : ∀ q, exponentialFlag (e q) = true)
    (hj : ∀ q, chooseAux binary64Arithmetic (u q * total) bounds.upper.toList 0 0 = some (j q))
    (ha : ∀ q, rssaAccept binary64Arithmetic bounds.lower[j q]! rates[j q]!
      (v q * bounds.upper[j q]!) = decide (q.val = k))
    (hfold : FoldFinite elapsed (List.ofFn e))
    (ht : clockFlag now ((List.ofFn e).foldl (· + ·) elapsed) total = true)
    (us es : List Binary64) (extraFuel : Nat := 0) :
    rssaProposals binary64Arithmetic (tapeSource Binary64) rates bounds now total (k + 1 + extraFuel) elapsed
      ⟨proposalFloatUniforms u v ++ us, List.ofFn e ++ es⟩ =
      .ok (some ⟨now + (List.ofFn e).foldl (· + ·) elapsed / total, j (Fin.last k)⟩, ⟨us, es⟩) := by
  induction k generalizing elapsed with
  | zero =>
    have hf : ExecFloat.Binary.isFinite (elapsed + e 0) = true := by
      have hx := hfold
      rw [List.ofFn_succ, List.ofFn_zero] at hx
      exact hx.2.2
    have hacc := ha 0
    simp only [Fin.val_zero, decide_true] at hacc
    have hc : clockFlag now (elapsed + e 0) total = true := by simpa using ht
    have hstep := rssa_step_float_flags rates bounds now total elapsed (e 0) (u 0) (v 0)
      (j 0) extraFuel (hu 0) (hv 0) (he 0) hf
      (hj 0) (fun _ => hc) us es
    simpa [proposalFloatUniforms, List.ofFn_succ, hacc, Nat.add_comm] using hstep
  | succ k ih =>
    have hacc : rssaAccept binary64Arithmetic bounds.lower[j 0]! rates[j 0]!
        (v 0 * bounds.upper[j 0]!) = false := by simpa using ha 0
    have hf : FoldFinite (elapsed + e 0) (List.ofFn (fun q : Fin (k + 1) => e q.succ)) := by
      have hx := hfold
      rw [List.ofFn_succ] at hx
      exact hx.2.2
    have ht' : clockFlag now ((List.ofFn (fun q : Fin (k + 1) => e q.succ)).foldl (· + ·)
        (elapsed + e 0)) total = true := by simpa only [List.ofFn_succ, List.foldl_cons] using ht
    have hi := ih (elapsed + e 0) (fun q => e q.succ) (fun q => u q.succ) (fun q => v q.succ)
      (fun q => j q.succ) (fun q => hu q.succ) (fun q => hv q.succ) (fun q => he q.succ)
      (fun q => hj q.succ) (by intro q; simpa only [Fin.val_succ, Nat.add_right_cancel_iff] using ha q.succ)
      hf ht'
    have hs := rssa_step_float_flags rates bounds now total elapsed (e 0) (u 0) (v 0)
      (j 0) (k + 1 + extraFuel) (hu 0) (hv 0) (he 0) (foldFinite_head _ _ hf) (hj 0)
      (by intro h; rw [hacc] at h; contradiction)
      (proposalFloatUniforms (fun q : Fin (k + 1) => u q.succ) (fun q => v q.succ) ++ us)
      (List.ofFn (fun q : Fin (k + 1) => e q.succ) ++ es)
    simp only [hacc, Bool.false_eq_true, ite_false] at hs
    simpa [proposalFloatUniforms, List.ofFn_succ, List.foldl_cons, Fin.last, Fin.succ,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs.trans hi

end JumpProcessesLean.Proofs
