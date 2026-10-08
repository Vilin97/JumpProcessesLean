import JumpProcessesLean.TreeRSSA
import JumpProcessesLean.Proofs.OperationalDirect

/-!
# The Tree-RSSA sum tree in real arithmetic

The root of the binary sum tree is the total of its leaves, and descending it with a
threshold below the total lands in the half-open cumulative interval of a positive leaf.
That is exactly the reaction selected by the native linear CDF search `weightedIndex`.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open Finset

lemma segSum_real (w : Array ℝ) : ∀ d lo,
    segSum realArithmetic w d lo = ∑ i ∈ range (2 ^ d), leafOf realArithmetic w (lo + i) := by
  intro d
  induction d with
  | zero => intro lo; simp [segSum]
  | succ d ih =>
    intro lo
    rw [segSum, ih, ih, pow_succ, mul_two, sum_range_add]
    simp only [realArithmetic, Nat.add_assoc]

lemma leafOf_nonneg (w : Array ℝ) (hw : ∀ x ∈ w.toList, 0 ≤ x) (i : Nat) :
    0 ≤ leafOf realArithmetic w i := by
  unfold leafOf
  split
  · exact hw _ (Array.getElem_mem_toList _)
  · exact le_refl _

/-- Leaves beyond the array are zero. -/
lemma sum_leafOf_eq_take (w : Array ℝ) (i : Nat) :
    ∑ k ∈ range i, leafOf realArithmetic w k = (w.toList.take i).sum := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, ih]
    by_cases hi : i < w.size
    · rw [List.take_add_one, List.sum_append]
      congr 1
      simp [leafOf, hi]
    · have hle : w.toList.length ≤ i := by rw [Array.length_toList]; exact not_lt.mp hi
      rw [List.take_of_length_le hle, List.take_of_length_le (by omega)]
      simp [leafOf, hi, realArithmetic]

lemma treeDepth_spec (m : Nat) : m ≤ 2 ^ treeDepth m := by
  unfold treeDepth
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (m - 1)
  rw [Nat.log2_eq_log_two]
  omega

lemma segSum_root (w : Array ℝ) (d : Nat) (hd : w.size ≤ 2 ^ d) :
    segSum realArithmetic w d 0 = w.toList.sum := by
  rw [segSum_real]
  simp only [zero_add]
  rw [sum_leafOf_eq_take, List.take_of_length_le (by simpa using hd)]

lemma realArithmetic_lt (a b : ℝ) : realArithmetic.lt a b = decide (a < b) := rfl
lemma realArithmetic_sub (a b : ℝ) : realArithmetic.sub a b = a - b := rfl
lemma realArithmetic_add (a b : ℝ) : realArithmetic.add a b = a + b := rfl
lemma realArithmetic_mul (a b : ℝ) : realArithmetic.mul a b = a * b := rfl

lemma segSum_succ_real (w : Array ℝ) (d lo : Nat) :
    segSum realArithmetic w (d + 1) lo =
      segSum realArithmetic w d lo + segSum realArithmetic w d (lo + 2 ^ d) := rfl

/-- The descent lands in the cumulative interval of a positive leaf. -/
lemma segDescend_interval (w : Array ℝ) (_hw : ∀ x ∈ w.toList, 0 ≤ x) : ∀ d lo x,
    0 ≤ x → x < segSum realArithmetic w d lo →
      ∃ i, segDescend realArithmetic w d lo x = lo + i ∧ i < 2 ^ d ∧
        ∑ k ∈ range i, leafOf realArithmetic w (lo + k) ≤ x ∧
        x < ∑ k ∈ range (i + 1), leafOf realArithmetic w (lo + k) := by
  intro d
  induction d with
  | zero =>
    intro lo x hx hlt
    refine ⟨0, by simp [segDescend], by simp, by simpa using hx, ?_⟩
    simpa [segSum] using hlt
  | succ d ih =>
    intro lo x hx hlt
    have hsplit := hlt
    rw [segSum_succ_real] at hsplit
    by_cases hleft : x < segSum realArithmetic w d lo
    · obtain ⟨i, hi, hid, hl, hu⟩ := ih lo x hx hleft
      refine ⟨i, ?_, by rw [pow_succ]; omega, hl, hu⟩
      rw [segDescend, realArithmetic_lt, decide_eq_true hleft, ite_eq_left rfl]
      exact hi
    · have hge : segSum realArithmetic w d lo ≤ x := not_lt.mp hleft
      have hx' : 0 ≤ x - segSum realArithmetic w d lo := by linarith
      have hlt' : x - segSum realArithmetic w d lo < segSum realArithmetic w d (lo + 2 ^ d) := by
        linarith
      obtain ⟨i, hi, hid, hl, hu⟩ := ih (lo + 2 ^ d) _ hx' hlt'
      have hleftSum : segSum realArithmetic w d lo =
          ∑ k ∈ range (2 ^ d), leafOf realArithmetic w (lo + k) := segSum_real w d lo
      have hshift : ∀ m, ∑ k ∈ range m, leafOf realArithmetic w (lo + 2 ^ d + k) =
          ∑ k ∈ range m, leafOf realArithmetic w (lo + (2 ^ d + k)) := by
        intro m
        apply sum_congr rfl
        intro k _
        rw [Nat.add_assoc]
      refine ⟨2 ^ d + i, ?_, by rw [pow_succ]; omega, ?_, ?_⟩
      · rw [segDescend, realArithmetic_lt, decide_eq_false hleft, ite_eq_right (by simp),
          realArithmetic_sub, hi]
        omega
      · rw [sum_range_add, ← hleftSum, ← hshift]
        linarith
      · rw [show 2 ^ d + i + 1 = 2 ^ d + (i + 1) by omega, sum_range_add, ← hleftSum, ← hshift]
        linarith

/-- The tree descent selects the same reaction as the native linear CDF search. -/
theorem segDescend_eq_weightedIndex (w : Array ℝ) (hw : ∀ x ∈ w.toList, 0 ≤ x) (d : Nat)
    (hd : w.size ≤ 2 ^ d) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hpos : 0 < w.toList.sum) :
    segDescend realArithmetic w d 0 (u * w.toList.sum) < w.size ∧
      weightedIndex realArithmetic w (realArithmetic.mul u (sumRates realArithmetic w)) =
        .ok (segDescend realArithmetic w d 0 (u * w.toList.sum)) := by
  have hx : 0 ≤ u * w.toList.sum := mul_nonneg hu0 hpos.le
  have hlt : u * w.toList.sum < segSum realArithmetic w d 0 := by
    rw [segSum_root w d hd]
    nlinarith
  obtain ⟨i, hi, _, hl, hu⟩ := segDescend_interval w hw d 0 _ hx hlt
  simp only [zero_add] at hi hl hu
  rw [sum_leafOf_eq_take] at hl hu
  have hisize : i < w.size := by
    by_contra hge
    have : (w.toList.take i).sum = w.toList.sum :=
      congrArg List.sum (List.take_of_length_le (by simpa using not_lt.mp hge))
    nlinarith
  refine ⟨by rw [hi]; exact hisize, ?_⟩
  have hc := chooseAux_interval w.toList hw (u * w.toList.sum) 0 0 i (by simpa using hisize)
    (by simpa using hl) (by simpa using hu)
  simp only [zero_add] at hc
  unfold weightedIndex
  rw [sumRates_real, realArithmetic_mul, show realArithmetic.zero = (0 : ℝ) from rfl, hc, hi]

end JumpProcessesLean.Proofs
