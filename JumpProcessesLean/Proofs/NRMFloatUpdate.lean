import JumpProcessesLean.Proofs.NRMFloatLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

def updateFresh {α : Type} (op : Arithmetic α) (old new : α) (j fired : Nat) : Bool :=
  op.lt op.zero new && !(j != fired && op.lt op.zero old)

def updateClock {α : Type} (op : Arithmetic α) (old new c e now : α) (j fired : Nat) : Option α :=
  if op.lt op.zero new then
    some (if j != fired && op.lt op.zero old then rescaleClock op now old new c
      else op.add now (op.div e new))
  else none

def updateTape {α : Type} {n : Nat} (op : Arithmetic α) (old new e : Fin n → α)
    (index fired : Nat) : List α :=
  (List.ofFn (fun j => if updateFresh op (old j) (new j) (index + j.val) fired then
    some (e j) else none)).filterMap id

/-- Flags of actual intermediate expressions, before observing the output. -/
def UpdateFlags {α : Type} (op : Arithmetic α) (old new c e now : α) (j fired : Nat) : Prop :=
  (op.lt op.zero new = true →
    (j != fired && op.lt op.zero old) = true →
      op.le now c = true ∧ (op.finite (rescaleClock op now old new c) &&
        op.le now (rescaleClock op now old new c)) = true) ∧
  (updateFresh op old new j fired = true →
    (op.finite e && op.lt op.zero e) = true ∧
      (op.finite (op.add now (op.div e new)) && op.lt now (op.add now (op.div e new))) = true)

theorem nrm_update_aux_flags {α : Type} {n : Nat} (op : Arithmetic α)
    (old new c e : Fin n → α) (now : α) (index fired : Nat)
    (hf : ∀ j, UpdateFlags op (old j) (new j) (c j) (e j) now (index + j.val) fired)
    (us es : List α) :
    nrmUpdateAllAux op (tapeSource α) fired now
      (List.ofFn old) (List.ofFn (fun j => if op.lt op.zero (old j) then some (c j) else none))
      (List.ofFn new) index ⟨us, updateTape op old new e index fired ++ es⟩ =
    .ok (List.ofFn (fun j => updateClock op (old j) (new j) (c j) (e j) now (index + j.val) fired),
      ⟨us, es⟩) := by
  induction n generalizing index with
  | zero => simp [nrmUpdateAllAux, updateTape, List.ofFn_zero]
  | succ n ih =>
    have htape : updateTape op old new e index fired =
        (if updateFresh op (old 0) (new 0) index fired then [e 0] else []) ++
        updateTape op (fun j => old j.succ) (fun j => new j.succ) (fun j => e j.succ) (index + 1) fired := by
      unfold updateTape
      rw [List.ofFn_succ]
      cases h : updateFresh op (old 0) (new 0) index fired <;>
        simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hi := ih (fun j => old j.succ) (fun j => new j.succ) (fun j => c j.succ)
      (fun j => e j.succ) (index + 1)
      (by intro j; simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf j.succ)
    simp only [List.ofFn_succ, htape, List.append_assoc, nrmUpdateAllAux]
    cases hn : op.lt op.zero (new 0) with
    | false =>
      simp [hn, updateFresh, updateClock, hi, Bind.bind, Except.bind, Pure.pure, Except.pure,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    | true =>
      cases hk : (index != fired && op.lt op.zero (old 0)) with
      | true =>
        have ho : op.lt op.zero (old 0) = true := by
          have h := hk
          rw [Bool.and_eq_true] at h
          exact h.2
        have hne : index ≠ fired := by
          have h := hk
          rw [Bool.and_eq_true] at h
          simpa using h.1
        have hp := (hf 0).1 hn hk
        simp [hn, hk, ho, hne, updateFresh, updateClock, hp.1, hp.2, hi,
          Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      | false =>
        have hfr : updateFresh op (old 0) (new 0) index fired = true := by simp [updateFresh, hn, hk]
        have hp := (hf 0).2 hfr
        have hd : drawExponential op (tapeSource α)
            (⟨us, e 0 :: (updateTape op (fun j => old j.succ) (fun j => new j.succ)
              (fun j => e j.succ) (index + 1) fired ++ es)⟩ : Tape α) =
            .ok (e 0, ⟨us, updateTape op (fun j => old j.succ) (fun j => new j.succ)
              (fun j => e j.succ) (index + 1) fired ++ es⟩) := by
          simp only [drawExponential, tapeSource, Bind.bind, Except.bind, hp.1]
          rfl
        simp [hn, hk, hfr, updateClock, hd, hp.2, hi,
          Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The actual public full-graph NRM float update, including inactive channels.
No returned-cache equality is assumed by this theorem. -/
theorem nrm_float_update_executes {n : Nat} (old new c e : Fin n → Binary64)
    (now : Binary64) (fired : Fin n)
    (hn : ∀ j, validRate binary64Arithmetic (new j) = true)
    (hnow : ExecFloat.Binary.isFinite now = true)
    (hf : ∀ j, UpdateFlags binary64Arithmetic (old j) (new j) (c j) (e j) now j.val fired.val)
    (us es : List Binary64) :
    nrmUpdate binary64Arithmetic (tapeSource Binary64)
      ⟨Array.ofFn old, Array.ofFn (fun j => if binary64Arithmetic.lt 0 (old j) then some (c j) else none)⟩
      (Array.ofFn new) fired.val now (List.range n).toArray
      ⟨us, updateTape binary64Arithmetic old new e 0 fired.val ++ es⟩ =
      .ok (⟨Array.ofFn new, Array.ofFn (fun j =>
        updateClock binary64Arithmetic (old j) (new j) (c j) (e j) now j.val fired.val)⟩, ⟨us, es⟩) := by
  have hv : ∀ a ∈ (Array.ofFn new).toList, validRate binary64Arithmetic a = true := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (by simpa using ha)
    exact hn j
  unfold nrmUpdate
  simp only [Array.size_ofFn, bne_self_eq_false, Bool.false_or,
    show (fired.val >= n) = false from by simp [Nat.not_le.mpr fired.isLt], decide_false, Bool.false_eq_true, ite_false]
  rw [show checkRates binary64Arithmetic (Array.ofFn new) = .ok () from checkRatesAux_valid _ _ hv 0]
  simp only [Bind.bind, Except.bind, show binary64Arithmetic.finite now = true from hnow,
    Bool.not_true, Bool.false_eq_true, ite_false, List.toList_toArray, ite_true, Array.toList_ofFn]
  have hex := nrm_update_aux_flags binary64Arithmetic old new c e now 0 fired.val (by simpa using hf) us es
  simp only [Nat.zero_add, show binary64Arithmetic.zero = (0 : Binary64) from rfl] at hex
  rw [hex]
  simp [Except.bind, Pure.pure, Except.pure, List.toArray_ofFn]

lemma rescale_input_error (ratio cf cr nf nr εc εn : ℝ)
    (hc : |cf - cr| ≤ εc) (hn : |nf - nr| ≤ εn) :
    |(nf + ratio * (cf - nf)) - (nr + ratio * (cr - nr))| ≤
      |ratio| * εc + |1 - ratio| * εn := by
  have he : (nf + ratio * (cf - nf)) - (nr + ratio * (cr - nr)) =
      ratio * (cf - cr) + (1 - ratio) * (nf - nr) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by simpa only [abs_mul] using
    (add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg ratio))
      (mul_le_mul_of_nonneg_left hn (abs_nonneg (1 - ratio)))))

end JumpProcessesLean.Proofs
