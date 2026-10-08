import JumpProcessesLean.TreeRSSA.Gen1
import JumpProcessesLean.Proofs.TreeRSSATree

/-!
# The flat sum tree

`TreeOK tree w d` says that the `FloatArray` holds the leaves `w` (zero padded) at
`2^d + i` and that every internal node is the sum of its two children. Then every node is
the specification's `segSum` of its leaves, the root is the specification's total, and
the array descent is the specification's `segDescend`. Building the tree and updating a
leaf with `fixPath` establish and preserve `TreeOK`. Nothing here uses floating-point
arithmetic laws: the node values are the same expressions.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1

/-! ### `FloatArray` through its data -/

@[simp] lemma floatArray_get!_eq (a : FloatArray) (i : Nat) : a.get! i = a.data[i]! := by
  cases a; rfl

@[simp] lemma floatArray_set!_data (a : FloatArray) (i : Nat) (v : Float) :
    (a.set! i v).data = a.data.set! i v := by
  cases a; rfl

lemma getElem!_set!_eq_ite (t : Array Float) (i j : Nat) (v : Float) (hi : i < t.size) :
    (t.set! i v)[j]! = if j = i then v else t[j]! := by
  split
  · subst_vars; exact Array.getElem!_set!_self _ _ _ hi
  · rename_i h; exact Array.getElem!_set!_ne _ _ _ _ (Ne.symm h)

/-! ### The invariant and the node values -/

/-- The flat sum tree over `w` with `2^d` leaves. -/
def TreeOK (tree : FloatArray) (w : Array Float) (d : Nat) : Prop :=
  tree.data.size = 2 * 2 ^ d ∧
    (∀ i < 2 ^ d, tree.data[2 ^ d + i]! = leafOf hostArithmetic w i) ∧
    ∀ k, 0 < k → k < 2 ^ d → tree.data[k]! = tree.data[2 * k]! + tree.data[2 * k + 1]!

lemma segSum_succ (w : Array Float) (h lo : Nat) :
    segSum hostArithmetic w (h + 1) lo =
      segSum hostArithmetic w h lo + segSum hostArithmetic w h (lo + 2 ^ h) := rfl

/-- Arithmetic of a node at height `h` and of its two children. -/
lemma node_children (P H k : Nat) (hP : P ≤ k * (2 * H)) (hP2 : k * (2 * H) < 2 * P)
    (hH : 0 < H) (hdiv : ∃ q, P = H * q) :
    0 < k ∧ k < P ∧ P ≤ 2 * k * H ∧ 2 * k * H < 2 * P ∧ P ≤ (2 * k + 1) * H ∧
      (2 * k + 1) * H < 2 * P ∧ 2 * k * H - P = k * (2 * H) - P ∧
      (2 * k + 1) * H - P = k * (2 * H) - P + H := by
  obtain ⟨q, rfl⟩ := hdiv
  have hPpos : 0 < H * q := by
    rcases Nat.eq_zero_or_pos (H * q) with h0 | h0
    · rw [h0] at hP2; omega
    · exact h0
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; rw [Nat.zero_mul] at hP; omega
    · exact h0
  have e1 : k * (2 * H) = 2 * (k * H) := by ring
  have e2 : 2 * k * H = 2 * (k * H) := by ring
  have e3 : (2 * k + 1) * H = 2 * (k * H) + H := by ring
  have hkq : k < q := by
    by_contra hc
    have : q * H ≤ k * H := Nat.mul_le_mul_right H (not_lt.mp hc)
    nlinarith
  have hkq' : (k + 1) * H ≤ q * H := Nat.mul_le_mul_right H hkq
  have e4 : (k + 1) * H = k * H + H := by ring
  have hkP : k < H * q := by nlinarith
  refine ⟨hk, hkP, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [mul_comm H q] at * <;> omega

theorem TreeOK.node {tree : FloatArray} {w : Array Float} {d : Nat} (h : TreeOK tree w d) :
    ∀ hgt k, 2 ^ d ≤ k * 2 ^ hgt → k * 2 ^ hgt < 2 * 2 ^ d →
      tree.data[k]! = segSum hostArithmetic w hgt (k * 2 ^ hgt - 2 ^ d) := by
  intro hgt
  induction hgt with
  | zero =>
    intro k hlo hhi
    simp only [pow_zero, mul_one] at hlo hhi ⊢
    have := h.2.1 (k - 2 ^ d) (by omega)
    rw [show 2 ^ d + (k - 2 ^ d) = k by omega] at this
    rw [this]
    rfl
  | succ hgt ih =>
    intro k hlo hhi
    rw [pow_succ, mul_comm (2 ^ hgt) 2] at hlo hhi ⊢
    have hle : hgt < d := by
      by_contra hc
      have hpow : 2 ^ d ≤ 2 ^ hgt := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc)
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp at hlo
        · exact hk
      nlinarith
    have hdiv : ∃ q, 2 ^ d = 2 ^ hgt * q :=
      ⟨2 ^ (d - hgt), by rw [← pow_add, Nat.add_sub_cancel' hle.le]⟩
    obtain ⟨hk, hkP, h1, h2, h3, h4, e1, e2⟩ :=
      node_children (2 ^ d) (2 ^ hgt) k hlo hhi (by positivity) hdiv
    rw [h.2.2 k hk hkP, ih (2 * k) h1 h2, ih (2 * k + 1) h3 h4, e1, e2, segSum_succ]

theorem TreeOK.root {tree : FloatArray} {w : Array Float} {d : Nat} (h : TreeOK tree w d) :
    tree.get! 1 = segSum hostArithmetic w d 0 := by
  have hn := h.node d 1 (by simp) (by simp)
  simp only [one_mul, Nat.sub_self] at hn
  rw [floatArray_get!_eq, hn]

lemma hostArithmetic_lt (a b : Float) : hostArithmetic.lt a b = decide (a < b) := rfl
lemma hostArithmetic_sub (a b : Float) : hostArithmetic.sub a b = a - b := rfl

theorem TreeOK.descend {tree : FloatArray} {w : Array Float} {d : Nat} (h : TreeOK tree w d) :
    ∀ hgt k x, 2 ^ d ≤ k * 2 ^ hgt → k * 2 ^ hgt < 2 * 2 ^ d →
      Gen1.descend tree hgt k x = segDescend hostArithmetic w hgt (k * 2 ^ hgt - 2 ^ d) x + 2 ^ d := by
  intro hgt
  induction hgt with
  | zero =>
    intro k x hlo hhi
    simp only [pow_zero, mul_one] at hlo hhi ⊢
    simp only [Gen1.descend, segDescend]
    omega
  | succ hgt ih =>
    intro k x hlo hhi
    rw [pow_succ, mul_comm (2 ^ hgt) 2] at hlo hhi ⊢
    have hle : hgt < d := by
      by_contra hc
      have hpow : 2 ^ d ≤ 2 ^ hgt := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc)
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp at hlo
        · exact hk
      nlinarith
    have hdiv : ∃ q, 2 ^ d = 2 ^ hgt * q :=
      ⟨2 ^ (d - hgt), by rw [← pow_add, Nat.add_sub_cancel' hle.le]⟩
    obtain ⟨hk, hkP, h1, h2, h3, h4, e1, e2⟩ :=
      node_children (2 ^ d) (2 ^ hgt) k hlo hhi (by positivity) hdiv
    have hleft : tree.get! (2 * k) = segSum hostArithmetic w hgt (k * (2 * 2 ^ hgt) - 2 ^ d) := by
      rw [floatArray_get!_eq, h.node hgt (2 * k) h1 h2, e1]
    rw [Gen1.descend, segDescend]
    rw [hleft, hostArithmetic_lt, hostArithmetic_sub]
    by_cases hx : x < segSum hostArithmetic w hgt (k * (2 * 2 ^ hgt) - 2 ^ d)
    · simp only [hx, decide_true, ↓reduceIte]
      rw [ih (2 * k) x h1 h2, e1]
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih (2 * k + 1) _ h3 h4, e2]

/-! ### Building the tree -/

lemma leafOf_eq (w : Array Float) (i : Nat) :
    leafOf hostArithmetic w i = if i < w.size then w[i]! else 0 := by
  unfold leafOf
  split
  · rename_i h; exact (getElem!_pos w i h).symm
  · rfl

lemma leafArray_spec (upper : Array Float) (d : Nat) :
    (leafArray upper d).data.size = 2 * 2 ^ d ∧
      ∀ i < 2 ^ d, (leafArray upper d).data[2 ^ d + i]! = leafOf hostArithmetic upper i := by
  refine ⟨by simp [leafArray], ?_⟩
  intro i hi
  have hlt : 2 ^ d + i < (leafArray upper d).data.size := by simp [leafArray]; omega
  rw [getElem!_pos (leafArray upper d).data (2 ^ d + i) hlt]
  simp [leafArray]

lemma fill_spec (P : Nat) : ∀ n (tree : FloatArray), n ≤ P → tree.data.size = 2 * P →
    (∀ k, n ≤ k → k < P → tree.data[k]! = tree.data[2 * k]! + tree.data[2 * k + 1]!) →
    (fill tree n).data.size = 2 * P ∧ (∀ i, P ≤ i → (fill tree n).data[i]! = tree.data[i]!) ∧
      ∀ k, 0 < k → k < P →
        (fill tree n).data[k]! = (fill tree n).data[2 * k]! + (fill tree n).data[2 * k + 1]! := by
  intro n
  induction n with
  | zero =>
    intro tree _ hs hH
    exact ⟨hs, fun _ _ => rfl, fun k _ hk => hH k (Nat.zero_le _) hk⟩
  | succ n ih =>
    intro tree hn hs hH
    rw [fill]
    split
    · rename_i h0
      subst h0
      exact ⟨hs, fun _ _ => rfl, fun k hk hk' => hH k hk hk'⟩
    · rename_i h0
      have hnP : n < 2 * P := by omega
      have hns : n < tree.data.size := by omega
      set t' := tree.set! n (tree.get! (2 * n) + tree.get! (2 * n + 1)) with ht'
      have ht'd : t'.data = tree.data.set! n (tree.data[2 * n]! + tree.data[2 * n + 1]!) := by
        simp [t']
      have hs' : t'.data.size = 2 * P := by rw [ht'd, Array.size_set!, hs]
      obtain ⟨r1, r2, r3⟩ := ih t' (by omega) hs' (by
        intro k hk hkP
        rw [ht'd]
        rw [getElem!_set!_eq_ite _ _ _ _ hns, getElem!_set!_eq_ite _ _ _ _ hns,
          getElem!_set!_eq_ite _ _ _ _ hns]
        by_cases hkn : k = n
        · subst hkn
          simp only [ite_true, show ¬(2 * k = k) by omega, show ¬(2 * k + 1 = k) by omega, ite_false]
        · simp only [hkn, show ¬(2 * k = n) by omega, show ¬(2 * k + 1 = n) by omega, ite_false]
          exact hH k (by omega) hkP)
      refine ⟨r1, fun i hi => ?_, r3⟩
      rw [r2 i hi, ht'd, getElem!_set!_eq_ite _ _ _ _ hns, if_neg (by omega)]

theorem buildTree_ok (upper : Array Float) (d : Nat) : TreeOK (buildTree upper d) upper d := by
  obtain ⟨hs, hl⟩ := leafArray_spec upper d
  obtain ⟨h1, h2, h3⟩ := fill_spec (2 ^ d) (2 ^ d) (leafArray upper d) le_rfl hs
    (fun k hk hk' => absurd hk' (by omega))
  exact ⟨h1, fun i hi => by rw [buildTree, h2 _ (by omega)]; exact hl i hi, h3⟩

/-! ### Updating a leaf -/

/-- `k` is a strict ancestor of node `c`. -/
def StrictAnc (c k : Nat) : Prop := ∃ m, 0 < m ∧ c / 2 ^ m = k

lemma strictAnc_iff (c k : Nat) : StrictAnc c k ↔ k = c / 2 ∨ StrictAnc (c / 2) k := by
  constructor
  · rintro ⟨m, hm, hk⟩
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => left; simpa using hk.symm
      | succ m =>
        right
        refine ⟨m + 1, by omega, ?_⟩
        rw [← hk, Nat.div_div_eq_div_mul, ← pow_succ']
  · rintro (rfl | ⟨m, hm, hk⟩)
    · exact ⟨1, by omega, by simp⟩
    · exact ⟨m + 1, by omega, by rw [pow_succ', ← Nat.div_div_eq_div_mul]; exact hk⟩

lemma not_strictAnc_one (k : Nat) (hk : 0 < k) : ¬StrictAnc 1 k := by
  rintro ⟨m, hm, h⟩
  have : 1 / 2 ^ m = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))
  omega

/-- Every node off the strict ancestors of `c` is the sum of its children. -/
def H2Off (t : Array Float) (P c : Nat) : Prop :=
  ∀ k, 0 < k → k < P → ¬StrictAnc c k → t[k]! = t[2 * k]! + t[2 * k + 1]!

lemma fixPath_spec (P : Nat) : ∀ n (tree : FloatArray) c, tree.data.size = 2 * P → c < 2 * P →
    H2Off tree.data P c →
    (fixPath tree n c).data.size = 2 * P ∧
      (∀ i, P ≤ i → (fixPath tree n c).data[i]! = tree.data[i]!) ∧
      H2Off (fixPath tree n c).data P (c / 2 ^ n) := by
  intro n
  induction n with
  | zero =>
    intro tree c hs _ hH
    refine ⟨hs, fun _ _ => rfl, ?_⟩
    simpa [fixPath] using hH
  | succ n ih =>
    intro tree c hs hc hH
    rw [fixPath]
    have hcs : c / 2 < tree.data.size := by omega
    set t' := tree.set! (c / 2) (tree.get! (2 * (c / 2)) + tree.get! (2 * (c / 2) + 1)) with ht'
    have ht'd : t'.data =
        tree.data.set! (c / 2) (tree.data[2 * (c / 2)]! + tree.data[2 * (c / 2) + 1]!) := by
      simp [t']
    have hs' : t'.data.size = 2 * P := by rw [ht'd, Array.size_set!, hs]
    have hH' : H2Off t'.data P (c / 2) := by
      intro k hk hkP hanc
      rw [ht'd, getElem!_set!_eq_ite _ _ _ _ hcs, getElem!_set!_eq_ite _ _ _ _ hcs,
        getElem!_set!_eq_ite _ _ _ _ hcs]
      by_cases hkc : k = c / 2
      · subst hkc
        simp only [ite_true, show ¬(2 * (c / 2) = c / 2) by omega,
          show ¬(2 * (c / 2) + 1 = c / 2) by omega, ite_false]
      · have h2k : ¬(2 * k = c / 2) := fun h => hanc ⟨1, by omega, by omega⟩
        have h2k1 : ¬(2 * k + 1 = c / 2) := fun h => hanc ⟨1, by omega, by omega⟩
        simp only [hkc, h2k, h2k1, ite_false]
        exact hH k hk hkP (fun ha => (strictAnc_iff c k).mp ha |>.elim hkc hanc)
    obtain ⟨r1, r2, r3⟩ := ih t' (c / 2) hs' (by omega) hH'
    refine ⟨r1, fun i hi => ?_, ?_⟩
    · rw [r2 i hi, ht'd, getElem!_set!_eq_ite _ _ _ _ hcs, if_neg (by omega)]
    · rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at r3

lemma leafOf_set (w : Array Float) (j i : Nat) (hj : j < w.size) (v : Float) :
    leafOf hostArithmetic (w.set! j v) i = if i = j then v else leafOf hostArithmetic w i := by
  rw [leafOf_eq, leafOf_eq, Array.size_set!]
  by_cases hij : i = j
  · subst hij
    rw [if_pos hj, Array.getElem!_set!_self _ _ _ hj, if_pos rfl]
  · rw [if_neg hij, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hij)]

/-- Setting leaf `j` and re-adding its root path gives the tree of the updated leaves. -/
theorem TreeOK.update {tree : FloatArray} {w : Array Float} {d : Nat} (h : TreeOK tree w d)
    (j : Nat) (hj : j < w.size) (hjd : j < 2 ^ d) (v : Float) :
    TreeOK (fixPath (tree.set! (2 ^ d + j) v) d (2 ^ d + j)) (w.set! j v) d := by
  obtain ⟨hs, hl, hH⟩ := h
  have hc : 2 ^ d + j < tree.data.size := by omega
  set t0 := tree.set! (2 ^ d + j) v with ht0
  have ht0d : t0.data = tree.data.set! (2 ^ d + j) v := by simp [t0]
  have hs0 : t0.data.size = 2 * 2 ^ d := by rw [ht0d, Array.size_set!, hs]
  have hH0 : H2Off t0.data (2 ^ d) (2 ^ d + j) := by
    intro k hk hkP hanc
    have h2k : ¬(2 * k = 2 ^ d + j) := fun h => hanc ⟨1, by omega, by omega⟩
    have h2k1 : ¬(2 * k + 1 = 2 ^ d + j) := fun h => hanc ⟨1, by omega, by omega⟩
    rw [ht0d, getElem!_set!_eq_ite _ _ _ _ hc, getElem!_set!_eq_ite _ _ _ _ hc,
      getElem!_set!_eq_ite _ _ _ _ hc, if_neg (by omega), if_neg h2k, if_neg h2k1]
    exact hH k hk hkP
  obtain ⟨r1, r2, r3⟩ := fixPath_spec (2 ^ d) d t0 (2 ^ d + j) hs0 (by omega) hH0
  have hroot : (2 ^ d + j) / 2 ^ d = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hroot] at r3
  refine ⟨r1, fun i hi => ?_, fun k hk hkP => r3 k hk hkP (not_strictAnc_one k hk)⟩
  rw [r2 _ (by omega), ht0d, getElem!_set!_eq_ite _ _ _ _ hc, leafOf_set w j i hj v, hl i hi]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, show ¬(2 ^ d + i = 2 ^ d + j) by omega]

end JumpProcessesLean.Proofs
