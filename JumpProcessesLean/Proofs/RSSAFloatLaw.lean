import JumpProcessesLean.Proofs.RSSAFloatExecution

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma foldFinite_result (acc : Binary64) (xs : List Binary64) (h : FoldFinite acc xs) :
    ExecFloat.Binary.isFinite (xs.foldl (· + ·) acc) = true := by
  induction xs generalizing acc with
  | nil => exact h
  | cons x xs ih => exact ih (acc + x) h.2.2

structure RSSAFloatCertificate {k : Nat} (rates : Array Binary64) (bounds : RateBounds Binary64)
    (now : Binary64) (e u v : Fin (k + 1) → Binary64) (er ur vr : Fin (k + 1) → ℝ)
    (δ η : ℝ) : Prop where
  boundsValid : checkBounds binary64Arithmetic rates bounds = .ok ()
  nowFinite : ExecFloat.Binary.isFinite now = true
  active : rates.any (binary64Arithmetic.lt binary64Arithmetic.zero) = true
  totalFinite : ExecFloat.Binary.isFinite (sumRates binary64Arithmetic bounds.upper) = true
  totalPositive : binary64Arithmetic.lt 0 (sumRates binary64Arithmetic bounds.upper) = true
  totalNonzero : Model.isZero (ExecFloat.Binary.toModel (sumRates binary64Arithmetic bounds.upper)) = false
  uniformU : ∀ q, uniformFlag (u q) = true
  uniformV : ∀ q, uniformFlag (v q) = true
  exponential : ∀ q, exponentialFlag (e q) = true
  proposal : ∀ q, RSSAProposalCertificate rates bounds (sumRates binary64Arithmetic bounds.upper)
    (u q) (v q) (ur q) (vr q) η
  elapsedFold : FoldFinite 0 (List.ofFn e)
  quotientFinite : ExecFloat.Binary.isFinite
    ((List.ofFn e).foldl (· + ·) 0 / sumRates binary64Arithmetic bounds.upper) = true
  clockValid : clockFlag now ((List.ofFn e).foldl (· + ·) 0) (sumRates binary64Arithmetic bounds.upper) = true
  timeBudget :
    floatEpsilon (floatReal now + floatReal ((List.ofFn e).foldl (· + ·) 0 / sumRates binary64Arithmetic bounds.upper)) +
    floatEpsilon (floatReal ((List.ofFn e).foldl (· + ·) 0) / floatReal (sumRates binary64Arithmetic bounds.upper)) +
    (foldRoundBudget 0 (List.ofFn e) + |((List.ofFn e).map floatReal).sum - (∑ q, er q)|) /
      floatReal (sumRates binary64Arithmetic bounds.upper) +
    |∑ q, er q| * foldRoundBudget 0 bounds.upper.toList /
      (floatReal (sumRates binary64Arithmetic bounds.upper) * (bounds.upper.toList.map floatReal).sum) ≤ δ

lemma rssa_float_calls_proposals (rates : Array Binary64) (bounds : RateBounds Binary64)
    (now : Binary64) (rng : Tape Binary64) (fuel : Nat)
    (hb : checkBounds binary64Arithmetic rates bounds = .ok ())
    (hn : ExecFloat.Binary.isFinite now = true)
    (ha : rates.any (binary64Arithmetic.lt binary64Arithmetic.zero) = true)
    (hT : ExecFloat.Binary.isFinite (sumRates binary64Arithmetic bounds.upper) = true)
    (hp : binary64Arithmetic.lt 0 (sumRates binary64Arithmetic bounds.upper) = true) :
    rssa binary64Arithmetic (tapeSource Binary64) rates bounds now rng fuel =
      rssaProposals binary64Arithmetic (tapeSource Binary64) rates bounds now
        (sumRates binary64Arithmetic bounds.upper) fuel 0 rng := by
  unfold rssa
  rw [hb]
  simp only [Bind.bind, Except.bind]
  rw [show binary64Arithmetic.finite now = true from hn, show binary64Arithmetic.finite
      (sumRates binary64Arithmetic bounds.upper) = true from hT, ha,
    show binary64Arithmetic.lt binary64Arithmetic.zero (sumRates binary64Arithmetic bounds.upper) = true from hp]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rfl

/-- Complete actual FloatLib RSSA on a first-success branch, with any suffix tape.
Rejected proposal clocks and the rounded upper-rate sum enter the explicit bound. -/
theorem rssa_float_certificate_refines {k : Nat} (rates : Array Binary64) (bounds : RateBounds Binary64)
    (now : Binary64) (e u v : Fin (k + 1) → Binary64) (er ur vr : Fin (k + 1) → ℝ)
    (δ η : ℝ) (hc : RSSAFloatCertificate rates bounds now e u v er ur vr δ η)
    (huppers : ∀ a ∈ bounds.upper.toList.map floatReal, 0 ≤ a)
    (hB : 0 < (bounds.upper.toList.map floatReal).sum) (hu : ∀ q, ur q ∈ Ioo 0 1)
    (i : Nat) (hbranch : ∀ q, proposalMark (rates.toList.map floatReal)
      (bounds.lower.toList.map floatReal) (bounds.upper.toList.map floatReal) (ur q, vr q) =
        if q.val < k then none else some i) (us es : List Binary64) (extraFuel : Nat := 0) :
    rssa binary64Arithmetic (tapeSource Binary64) rates bounds now
      ⟨proposalFloatUniforms u v ++ us, List.ofFn e ++ es⟩ (k + 1 + extraFuel) =
      .ok (some ⟨now + (List.ofFn e).foldl (· + ·) 0 / sumRates binary64Arithmetic bounds.upper, i⟩, ⟨us, es⟩) ∧
    |floatReal (now + (List.ofFn e).foldl (· + ·) 0 / sumRates binary64Arithmetic bounds.upper) -
      (floatReal now + (∑ q, er q) / (bounds.upper.toList.map floatReal).sum)| ≤ δ := by
  have hsel : ∀ q, ∃ j, chooseAux binary64Arithmetic
      (u q * sumRates binary64Arithmetic bounds.upper) bounds.upper.toList 0 0 = some j := by
    intro q
    obtain ⟨j, hj⟩ := chooseAux_exists (bounds.upper.toList.map floatReal) huppers
      (ur q * (bounds.upper.toList.map floatReal).sum) 0 (by nlinarith [(hu q).1]) (by nlinarith [(hu q).2]) 0
    have hs := chooseAux_float_margin bounds.upper.toList 0
      (u q * sumRates binary64Arithmetic bounds.upper) (ur q * (bounds.upper.toList.map floatReal).sum)
      η (hc.proposal q).upperFold (hc.proposal q).thresholdFinite (hc.proposal q).thresholdError
      (by intro j hj; exact (hc.proposal q).prefixBudget j (by simpa using hj))
      (by intro j hj; simpa only [floatReal_zero, zero_add] using (hc.proposal q).cdfMargin j (by simpa using hj)) 0
    simp only [floatReal_zero] at hs
    exact ⟨j, hs.trans hj⟩
  choose j hj using hsel
  have hmark (q : Fin (k + 1)) :
      (if rssaAccept binary64Arithmetic bounds.lower[j q]! rates[j q]! (v q * bounds.upper[j q]!)
        then some (j q) else none) = if q.val < k then none else some i := by
    have hm := rssa_proposal_certificate_refines rates bounds _ (u q) (v q) (ur q) (vr q) η
      (hc.proposal q) huppers hB (hu q)
    rw [hbranch q] at hm
    simpa only [floatProposalMark, hj] using hm
  have ha : ∀ q, rssaAccept binary64Arithmetic bounds.lower[j q]! rates[j q]!
      (v q * bounds.upper[j q]!) = decide (q.val = k) := by
    intro q
    have hm := hmark q
    by_cases hq : q.val < k
    · simp only [hq, ite_true] at hm
      have hrej : rssaAccept binary64Arithmetic bounds.lower[j q]! rates[j q]!
          (v q * bounds.upper[j q]!) = false := by
        cases h : rssaAccept binary64Arithmetic bounds.lower[j q]! rates[j q]!
          (v q * bounds.upper[j q]!) <;> simp_all
      simpa [Nat.ne_of_lt hq] using hrej
    · have heq : q.val = k := by omega
      simp only [hq, ite_false] at hm
      have hacc : rssaAccept binary64Arithmetic bounds.lower[j q]! rates[j q]!
          (v q * bounds.upper[j q]!) = true := by
        cases h : rssaAccept binary64Arithmetic bounds.lower[j q]! rates[j q]!
          (v q * bounds.upper[j q]!) <;> simp_all
      simpa [heq] using hacc
  have hlast : j (Fin.last k) = i := by
    have hm := hmark (Fin.last k)
    simp only [ha, Fin.val_last, decide_true, ite_true, lt_self_iff_false, ite_false, Option.some.injEq] at hm
    exact hm
  have hex := rssa_float_branch_executes rates bounds now (sumRates binary64Arithmetic bounds.upper)
    0 e u v j hc.uniformU hc.uniformV hc.exponential hj ha hc.elapsedFold hc.clockValid us es extraFuel
  rw [hlast] at hex
  constructor
  · rw [rssa_float_calls_proposals _ _ _ _ _ hc.boundsValid hc.nowFinite hc.active hc.totalFinite hc.totalPositive]
    exact hex
  · let E := (List.ofFn e).foldl (· + ·) 0
    let T := sumRates binary64Arithmetic bounds.upper
    have hE : ExecFloat.Binary.isFinite E = true := by
      exact foldFinite_result 0 (List.ofFn e) hc.elapsedFold
    have hout : ExecFloat.Binary.isFinite (now + E / T) = true := by
      have h := hc.clockValid
      have hp : binary64Arithmetic.finite (now + E / T) = true ∧
          binary64Arithmetic.lt now (now + E / T) = true := by
        simpa only [clockFlag, Bool.and_eq_true] using h
      exact hp.1
    have hTp : 0 < floatReal T := by
      have hp : (0 : Binary64) < T := of_decide_eq_true hc.totalPositive
      simpa only [floatReal_zero] using (float_lt_real 0 T float_zero_finite hc.totalFinite).mp hp
    have hsum := float_fold_sum_error 0 bounds.upper.toList (hc.proposal 0).upperFold
    rw [← sumRates_binary64, floatReal_zero, zero_add] at hsum
    have hacc := float_fold_sum_error 0 (List.ofFn e) hc.elapsedFold
    simp only [floatReal_zero, zero_add] at hacc
    have hEerr : |floatReal E - (∑ q, er q)| ≤
        foldRoundBudget 0 (List.ofFn e) + |((List.ofFn e).map floatReal).sum - (∑ q, er q)| :=
      (abs_sub_le _ _ _).trans (add_le_add hacc (le_refl _))
    have hclock := float_clock_time_error now E T hc.nowFinite hE hc.totalFinite
      hc.totalNonzero hc.quotientFinite hout
    have hdiv := quotient_input_error (floatReal E) (∑ q, er q) (floatReal T)
      (bounds.upper.toList.map floatReal).sum hTp hB _ hsum
    have hd := hdiv.trans (add_le_add (div_le_div_of_nonneg_right hEerr hTp.le) (le_refl _))
    have ht : |floatReal (now + E / T) - (floatReal now + (∑ q, er q) /
        (bounds.upper.toList.map floatReal).sum)| ≤
        floatEpsilon (floatReal now + floatReal (E / T)) + floatEpsilon (floatReal E / floatReal T) +
        (foldRoundBudget 0 (List.ofFn e) + |((List.ofFn e).map floatReal).sum - (∑ q, er q)|) / floatReal T +
        |∑ q, er q| * foldRoundBudget 0 bounds.upper.toList /
          (floatReal T * (bounds.upper.toList.map floatReal).sum) := by
      have h := (abs_sub_le (floatReal (now + E / T)) (floatReal now + floatReal E / floatReal T)
        (floatReal now + (∑ q, er q) / (bounds.upper.toList.map floatReal).sum)).trans
          (add_le_add hclock (by simpa only [add_sub_add_left_eq_sub] using hd))
      simpa only [add_assoc] using h
    exact ht.trans hc.timeBudget

end JumpProcessesLean.Proofs
