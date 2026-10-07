import JumpProcessesLean.Proofs.DirectFloatLaw
import JumpProcessesLean.Proofs.OperationalNRM

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

theorem nrmInitializeAux_flags {α : Type} (op : Arithmetic α) {n : Nat}
    (rates e : Fin n → α) (now : α)
    (hr : ∀ j, op.lt op.zero (rates j) = true)
    (he : ∀ j, (op.finite (e j) && op.lt op.zero (e j)) = true)
    (ht : ∀ j, (op.finite (op.add now (op.div (e j) (rates j))) &&
      op.lt now (op.add now (op.div (e j) (rates j)))) = true)
    (us es : List α) :
    nrmInitializeAux op (tapeSource α) now (List.ofFn rates)
      ⟨us, List.ofFn e ++ es⟩ =
      .ok (List.ofFn (fun j => some (op.add now (op.div (e j) (rates j)))), ⟨us, es⟩) := by
  induction n with
  | zero => simp [List.ofFn_zero, nrmInitializeAux]
  | succ n ih =>
    have hi := ih (fun j => rates j.succ) (fun j => e j.succ)
      (fun j => hr j.succ) (fun j => he j.succ) (fun j => ht j.succ)
    have hd : drawExponential op (tapeSource α)
        (⟨us, e 0 :: (List.ofFn (fun j : Fin n => e j.succ) ++ es)⟩ : Tape α) =
      .ok (e 0, ⟨us, List.ofFn (fun j : Fin n => e j.succ) ++ es⟩) := by
      simp only [drawExponential, tapeSource, Bind.bind, Except.bind, he 0]
      rfl
    simp only [List.ofFn_succ, List.cons_append, nrmInitializeAux, hr 0,
      ite_true, hd, Bind.bind, Except.bind, ht 0, Bool.not_true,
      Bool.false_eq_true, ite_false, Pure.pure, Except.pure, hi]

structure NRMFloatCertificate {n : Nat} (rates e : Fin n → Binary64)
    (er : Fin n → ℝ) (η : ℝ) : Prop where
  validRates : ∀ j, validRate binary64Arithmetic (rates j) = true
  positiveRates : ∀ j, binary64Arithmetic.lt 0 (rates j) = true
  rateNonzero : ∀ j, Model.isZero (ExecFloat.Binary.toModel (rates j)) = false
  exponentialValid : ∀ j, (binary64Arithmetic.finite (e j) && binary64Arithmetic.lt 0 (e j)) = true
  quotientFinite : ∀ j, ExecFloat.Binary.isFinite (e j / rates j) = true
  clockValid : ∀ j, (binary64Arithmetic.finite (0 + e j / rates j) &&
    binary64Arithmetic.lt 0 (0 + e j / rates j)) = true
  clockBudget : ∀ j,
    floatEpsilon (floatReal (e j / rates j)) +
    floatEpsilon (floatReal (e j) / floatReal (rates j)) +
    |floatReal (e j) - er j| / floatReal (rates j) ≤ η

noncomputable def nrmFloatSample {n : Nat} (rates e : Fin n → Binary64) : Option (Event Binary64) :=
  match nrmInitialize binary64Arithmetic (tapeSource Binary64) (Array.ofFn rates) 0
    ⟨[], List.ofFn e⟩ with
  | .ok (state, _) => nrmNext binary64Arithmetic state
  | _ => none

noncomputable def nrmFloatTime {n : Nat} (rates e : Fin n → Binary64) : ℝ :=
  (nrmFloatSample rates e).map (fun e => floatReal e.time) |>.getD 0

noncomputable def nrmFloatMark {n : Nat} (rates e : Fin n → Binary64) : Option Nat :=
  (nrmFloatSample rates e).map Event.reaction

/-- Complete FloatLib NRM initialization and next-event selection, with numerical
source budgets and a winner gap. Agreement is derived, not included in the certificate. -/
theorem nrm_float_certificate_refines {n : Nat} (rates e : Fin (n + 1) → Binary64)
    (er : Fin (n + 1) → ℝ) (η : ℝ) (hc : NRMFloatCertificate rates e er η)
    (i : Fin (n + 1))
    (hgap : ∀ j, j ≠ i → er i / floatReal (rates i) + 2 * η < er j / floatReal (rates j)) :
    |nrmFloatTime rates e - er i / floatReal (rates i)| ≤ η ∧
      nrmFloatMark rates e = some i.val := by
  have hrf (j : Fin (n + 1)) : ExecFloat.Binary.isFinite (rates j) = true := by
    have hv := hc.validRates j
    have hp : binary64Arithmetic.finite (rates j) = true ∧
        binary64Arithmetic.le binary64Arithmetic.zero (rates j) = true := by
      simpa only [validRate, Bool.and_eq_true] using hv
    exact hp.1
  have hef (j : Fin (n + 1)) : ExecFloat.Binary.isFinite (e j) = true := by
    have hp : binary64Arithmetic.finite (e j) = true ∧ binary64Arithmetic.lt 0 (e j) = true := by
      simpa only [Bool.and_eq_true] using hc.exponentialValid j
    exact hp.1
  have hcf (j : Fin (n + 1)) : ExecFloat.Binary.isFinite (0 + e j / rates j) = true := by
    have hp : binary64Arithmetic.finite (0 + e j / rates j) = true ∧
        binary64Arithmetic.lt 0 (0 + e j / rates j) = true := by
      simpa only [Bool.and_eq_true] using hc.clockValid j
    exact hp.1
  have hrp (j : Fin (n + 1)) : 0 < floatReal (rates j) := by
    have hp : (0 : Binary64) < rates j := of_decide_eq_true (hc.positiveRates j)
    simpa only [floatReal_zero] using (float_lt_real 0 _ float_zero_finite (hrf j)).mp hp
  have hclock (j : Fin (n + 1)) :
      |floatReal (0 + e j / rates j) - er j / floatReal (rates j)| ≤ η := by
    have hb := float_clock_time_error 0 (e j) (rates j) float_zero_finite
      (hef j) (hrf j) (hc.rateNonzero j) (hc.quotientFinite j) (hcf j)
    simp only [floatReal_zero, zero_add] at hb
    have hs : |floatReal (e j) / floatReal (rates j) - er j / floatReal (rates j)| =
        |floatReal (e j) - er j| / floatReal (rates j) := by
      rw [← sub_div, abs_div, abs_of_pos (hrp j)]
    exact ((abs_sub_le _ _ _).trans (add_le_add hb (le_of_eq hs))).trans
      (by simpa only [add_assoc] using hc.clockBudget j)
  have hvalid : ∀ a ∈ (Array.ofFn rates).toList, validRate binary64Arithmetic a = true := by
    simp only [Array.toList_ofFn]
    intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha; exact hc.validRates j
  have hinit : nrmInitialize binary64Arithmetic (tapeSource Binary64) (Array.ofFn rates) 0
      ⟨[], List.ofFn e⟩ = .ok
        (⟨Array.ofFn rates, Array.ofFn (fun j => some (0 + e j / rates j))⟩, ⟨[], []⟩) := by
    unfold nrmInitialize
    rw [show checkRates binary64Arithmetic (Array.ofFn rates) = .ok () from
      checkRatesAux_valid _ _ hvalid 0]
    simp only [Bind.bind, Except.bind, show binary64Arithmetic.finite (0 : Binary64) = true from float_zero_finite,
      Bool.not_true, Bool.false_eq_true, ite_false, Array.toList_ofFn]
    have hx := nrmInitializeAux_flags binary64Arithmetic rates e 0 hc.positiveRates hc.exponentialValid hc.clockValid [] []
    simp only [List.append_nil] at hx
    rw [hx]
    simp only [binary64Arithmetic, Except.bind, Pure.pure, Except.pure, List.toArray_ofFn]
  have hnext := nrm_float_winner_approx rates (fun j => 0 + e j / rates j)
    (fun j => er j / floatReal (rates j)) i η hcf hclock hgap
  unfold nrmFloatTime nrmFloatMark nrmFloatSample
  rw [hinit]
  dsimp only
  rw [hnext.1]
  exact ⟨hnext.2, rfl⟩

end JumpProcessesLean.Proofs
