import JumpProcessesLean.RealBackend
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

namespace JumpProcessesLean.Proofs

/-- The shared executable selector selects channel i whenever the threshold lies in
its half-open propensity interval. Zero-width intervals are excluded automatically. -/
theorem chooseAux_interval (weights : List ℝ) (hn : ∀ a ∈ weights, 0 ≤ a)
    (x cumulative : ℝ) (index i : Nat) (hi : i < weights.length)
    (hlower : cumulative + (weights.take i).sum ≤ x)
    (hupper : x < cumulative + (weights.take (i + 1)).sum) :
    chooseAux realArithmetic x weights cumulative index = some (index + i) := by
  induction weights generalizing cumulative index i with
  | nil => simp at hi
  | cons a rest ih =>
    have hrest : ∀ b ∈ rest, 0 ≤ b := fun b hb => hn b (by simp [hb])
    cases i with
    | zero =>
      have ha : 0 < a := by
        simp only [List.take_zero, List.sum_nil, add_zero] at hlower
        simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil,
          add_zero] at hupper
        linarith
      simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil,
        add_zero] at hupper
      simp [chooseAux, realArithmetic, ha, hupper]
    | succ i =>
      have hs : 0 ≤ (rest.take i).sum :=
        List.sum_nonneg (fun b hb => hrest b (List.mem_of_mem_take hb))
      have hx : cumulative + a ≤ x := by
        simp only [List.take_succ_cons, List.sum_cons] at hlower
        linarith
      have hnot : ¬(0 < a ∧ x < cumulative + a) := by
        intro h
        linarith [h.2]
      have hl : cumulative + a + (rest.take i).sum ≤ x := by
        simpa only [List.take_succ_cons, List.sum_cons, add_assoc] using hlower
      have hu : x < cumulative + a + (rest.take (i + 1)).sum := by
        have hp := hupper
        rw [List.take_succ_cons, List.sum_cons] at hp
        simpa only [add_assoc] using hp
      have hi' : i < rest.length := by simpa using hi
      simp only [chooseAux, realArithmetic, ← Bool.decide_and, hnot, decide_false,
        Bool.false_eq_true, ite_false]
      simpa only [realArithmetic, Nat.add_assoc, Nat.add_comm 1 i] using
        ih hrest (cumulative + a) (index + 1) i hi' hl hu

end JumpProcessesLean.Proofs
