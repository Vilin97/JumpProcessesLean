import JumpProcessesLean.TreeRSSA.Gen23

/-!
# Tree-RSSA, generation 24: the descent ends in a branch-free pair of levels

Generation 23's two-level descent takes its last two levels as one more step of two branches.
Generation 24 computes the leaf of a node two levels above the leaves as `4k + c`, where the
offset `c` comes from the same three comparisons, written as nested selections of constants
that the C compiler turns into flag arithmetic: on trees of even depth the descent ends
without a branch on its last two levels. The rest is generation 23's.
-/

namespace JumpProcessesLean.TreeRSSA.Gen24

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)
open Gen18 (ChangeW DepW Compiled compileW staleW bracketLo bracketHi ff2 ofCounts toCounts
  allSmall twoPow25)
open Gen19 (CacheV toCache rateMax)
open Gen20 (Bounds boundsOK boundsOK_spec Sized size_uset one_toNat)
open Gen21 (RxW buildRx RxAt RxOK buildRx_ok evalR apply1 smallR)
open Gen22 (Level level_lt level_ge level_two_mul_lt level_child two_toNat two_le_toNat
  toNat_sub_two level_root applyR applyR_size refreshFromR refreshFromR_sized)

/-- Generation 11's word descent, compiled in this module so that the driver inlines it. -/
def descendW (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) : USize :=
  if hk : k < P then
    have hk' : k.toNat < P.toNat := hk
    have h2 : (2 * k).toNat < tree.size := by rw [Gen11.usize_two_mul k (by omega)]; omega
    let left := tree.uget (2 * k) h2
    if x < left then
      descendW tree P hP hP2 (2 * k) (by rw [Gen11.usize_two_mul k (by omega)]; omega) x
    else
      descendW tree P hP hP2 (2 * k + 1) (by rw [Gen11.usize_two_mul_add_one k (by omega)]; omega)
        (x - left)
  else k
termination_by P.toNat - k.toNat
decreasing_by
  · have := (show k.toNat < P.toNat from hk)
    rw [Gen11.usize_two_mul k (by omega)]; omega
  · have := (show k.toNat < P.toNat from hk)
    rw [Gen11.usize_two_mul_add_one k (by omega)]; omega

/-- The descent ends below `2P`. -/
theorem descendW_lt (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      k.toNat < 2 * P.toNat → (descendW tree P hP hP2 k hk0 x).toNat < 2 * P.toNat := by
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm hk2
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
    exact hk2
  | succ m ih =>
    intro k hk0 x hm hk2
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega) (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega) (by rw [h21]; omega)
    · rw [descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
      exact hk2

/-! ## Two levels per step -/

theorem three_toNat : (3 : USize).toNat = 3 := by
  rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]

theorem three_le_toNat {d : USize} (h : 3 ≤ d) : 3 ≤ d.toNat := by
  have := (USize.le_iff_toNat_le).mp h; rw [three_toNat] at this; exact this

theorem two_le_of_three_le {d : USize} (h : 3 ≤ d) : 2 ≤ d :=
  (USize.le_iff_toNat_le).mpr (by rw [two_toNat]; have := three_le_toNat h; omega)

/-- Two levels per step, `d` levels above the leaves: generation 21's descent with half its loop
tests. -/
def descend2 (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (d k : USize) (hk : Level P d k) (x : Float) : USize :=
  if h3 : 3 ≤ d then
    have hd3 : 3 ≤ d.toNat := three_le_toNat h3
    have h2 : 2 ≤ d := two_le_of_three_le h3
    have hd2 : 2 ≤ d.toNat := two_le_toNat h2
    have hkP := level_lt hk (by omega)
    have e2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
    have e21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
    have hl0 : Level P (d - 1) (2 * k) := level_child hk (by omega) _ (Or.inl e2) _
      (Gen16.pred_toNat d (by intro h; rw [h] at hd2; simp at hd2))
    have hl1 : Level P (d - 1) (2 * k + 1) := level_child hk (by omega) _ (Or.inr e21) _
      (Gen16.pred_toNat d (by intro h; rw [h] at hd2; simp at hd2))
    have hd1 : 1 ≤ (d - 1).toNat := by
      rw [Gen16.pred_toNat d (by intro h; rw [h] at hd2; simp at hd2)]; omega
    have h0P := level_lt hl0 hd1
    have h1P := level_lt hl1 hd1
    have e00 : (2 * (2 * k)).toNat = 2 * (2 * k).toNat := Gen11.usize_two_mul _ (by omega)
    have e01 : (2 * (2 * k) + 1).toNat = 2 * (2 * k).toNat + 1 :=
      Gen11.usize_two_mul_add_one _ (by omega)
    have e10 : (2 * (2 * k + 1)).toNat = 2 * (2 * k + 1).toNat := Gen11.usize_two_mul _ (by omega)
    have e11 : (2 * (2 * k + 1) + 1).toNat = 2 * (2 * k + 1).toNat + 1 :=
      Gen11.usize_two_mul_add_one _ (by omega)
    have hdd : (d - 2).toNat = (d - 1).toNat - 1 := by
      rw [toNat_sub_two h2, Gen16.pred_toNat d (by intro h; rw [h] at hd2; simp at hd2)]; omega
    let l := tree.uget (2 * k) (by omega)
    if x < l then
      let ll := tree.uget (2 * (2 * k)) (by omega)
      if x < ll then
        descend2 tree P hP hP2 (d - 2) (2 * (2 * k)) (level_child hl0 hd1 _ (Or.inl e00) _ hdd) x
      else
        descend2 tree P hP hP2 (d - 2) (2 * (2 * k) + 1) (level_child hl0 hd1 _ (Or.inr e01) _ hdd)
          (x - ll)
    else
      let x1 := x - l
      let rl := tree.uget (2 * (2 * k + 1)) (by omega)
      if x1 < rl then
        descend2 tree P hP hP2 (d - 2) (2 * (2 * k + 1)) (level_child hl1 hd1 _ (Or.inl e10) _ hdd) x1
      else
        descend2 tree P hP hP2 (d - 2) (2 * (2 * k + 1) + 1)
          (level_child hl1 hd1 _ (Or.inr e11) _ hdd) (x1 - rl)
  else if hp : d = 2 then
    have hd2 : d.toNat = 2 := by rw [hp, two_toNat]
    have hkP := level_lt hk (by omega)
    have e2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
    have e21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
    have hdp : (d - 1).toNat = d.toNat - 1 :=
      Gen16.pred_toNat d (by intro h; rw [h] at hd2; simp at hd2)
    have hl0 : Level P (d - 1) (2 * k) := level_child hk (by omega) _ (Or.inl e2) _ hdp
    have hl1 : Level P (d - 1) (2 * k + 1) := level_child hk (by omega) _ (Or.inr e21) _ hdp
    have h0P := level_lt hl0 (by omega)
    have h1P := level_lt hl1 (by omega)
    have e00 : (2 * (2 * k)).toNat = 2 * (2 * k).toNat := Gen11.usize_two_mul _ (by omega)
    have e10 : (2 * (2 * k + 1)).toNat = 2 * (2 * k + 1).toNat := Gen11.usize_two_mul _ (by omega)
    let l := tree.uget (2 * k) (by omega)
    let ll := tree.uget (2 * (2 * k)) (by omega)
    let rl := tree.uget (2 * (2 * k + 1)) (by omega)
    4 * k + (if x < l then (if x < ll then 0 else 1) else (if x - l < rl then 2 else 3))
  else if h1 : d = 1 then
    have hd1 : d.toNat = 1 := by rw [h1]; rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
    have hkP := level_lt hk (by omega)
    have e2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
    let l := tree.uget (2 * k) (by omega)
    if x < l then 2 * k else 2 * k + 1
  else k
termination_by d.toNat
decreasing_by
  all_goals (rw [toNat_sub_two h2]; omega)

/-- The two-level descent is the word descent. -/
theorem four_mul_add_toNat {k : USize} (c : USize) (h : 4 * k.toNat + 3 < USize.size)
    (hc : c.toNat ≤ 3) : (4 * k + c).toNat = 4 * k.toNat + c.toNat := by
  have h4 : (4 : USize).toNat = 4 := by
    rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
  have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
  have hlt : 4 * k.toNat < 2 ^ System.Platform.numBits := by omega
  rw [USize.toNat_add, USize.toNat_mul, h4, Nat.mod_eq_of_lt hlt]
  exact Nat.mod_eq_of_lt (by omega)

theorem usize_lit_toNat (c : Nat) (hc : c ≤ 3) : (OfNat.ofNat c : USize).toNat = c := by
  have : c < USize.size := by
    rcases USize.size_eq with h | h <;> rw [h] <;> omega
  exact USize.toNat_ofNat_of_lt' this

/-- The two-level descent is the word descent. -/
theorem descend2_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (d k : USize) (hk : Level P d k) (hk0 : 0 < k.toNat) (x : Float), d.toNat ≤ m →
      descend2 tree P hP hP2 d k hk x = descendW tree P hP hP2 k hk0 x := by
  intro m
  induction m with
  | zero =>
    intro d k hk hk0 x hm
    have hd0 : d.toNat = 0 := by omega
    have h3 : ¬ 3 ≤ d := fun h => by have := three_le_toNat h; omega
    have hp : ¬ d = 2 := fun h => by rw [h, two_toNat] at hd0; omega
    have h1 : ¬ d = 1 := fun h => by
      rw [h] at hd0; rcases USize.size_eq with h' | h' <;> simp [USize.toNat_ofNat, h'] at hd0
    have g := level_ge hk hd0
    have nk : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [descend2, dite_eq_right h3, dite_eq_right hp, dite_eq_right h1, descendW,
      dite_eq_right_iff.mpr (fun h => absurd h nk)]
  | succ m ih =>
    intro d k hk hk0 x hm
    by_cases h3 : 3 ≤ d
    · have h2 : 2 ≤ d := two_le_of_three_le h3
      have hd2 : 2 ≤ d.toNat := two_le_toNat h2
      have hkP := level_lt hk (by omega)
      have e2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have e21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      have hdp : (d - 1).toNat = d.toNat - 1 :=
        Gen16.pred_toNat d (by intro h; rw [h] at hd2; simp at hd2)
      have hl0 : Level P (d - 1) (2 * k) := level_child hk (by omega) _ (Or.inl e2) _ hdp
      have hl1 : Level P (d - 1) (2 * k + 1) := level_child hk (by omega) _ (Or.inr e21) _ hdp
      have h0P := level_lt hl0 (by omega)
      have h1P := level_lt hl1 (by omega)
      have hkP' : k < P := hkP
      have h0P' : 2 * k < P := h0P
      have h1P' : 2 * k + 1 < P := h1P
      rw [descend2, dite_eq_left h3, descendW, dite_eq_left_of_eq_true (eq_true hkP')]
      simp only []
      split
      · rw [descendW, dite_eq_left_of_eq_true (eq_true h0P')]
        simp only []
        split
        · exact ih _ _ _ _ _ (by rw [toNat_sub_two h2]; omega)
        · exact ih _ _ _ _ _ (by rw [toNat_sub_two h2]; omega)
      · rw [descendW, dite_eq_left_of_eq_true (eq_true h1P')]
        simp only []
        split
        · exact ih _ _ _ _ _ (by rw [toNat_sub_two h2]; omega)
        · exact ih _ _ _ _ _ (by rw [toNat_sub_two h2]; omega)
    · by_cases hp : d = 2
      · have hd2 : d.toNat = 2 := by rw [hp, two_toNat]
        have hkP := level_lt hk (by omega)
        have e2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
        have e21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
        have hdp : (d - 1).toNat = d.toNat - 1 :=
          Gen16.pred_toNat d (by intro h; rw [h] at hd2; simp at hd2)
        have hl0 : Level P (d - 1) (2 * k) := level_child hk (by omega) _ (Or.inl e2) _ hdp
        have hl1 : Level P (d - 1) (2 * k + 1) := level_child hk (by omega) _ (Or.inr e21) _ hdp
        have h0P := level_lt hl0 (by omega)
        have h1P := level_lt hl1 (by omega)
        have e00 : (2 * (2 * k)).toNat = 2 * (2 * k).toNat := Gen11.usize_two_mul _ (by omega)
        have e01 : (2 * (2 * k) + 1).toNat = 2 * (2 * k).toNat + 1 :=
          Gen11.usize_two_mul_add_one _ (by omega)
        have e10 : (2 * (2 * k + 1)).toNat = 2 * (2 * k + 1).toNat :=
          Gen11.usize_two_mul _ (by omega)
        have e11 : (2 * (2 * k + 1) + 1).toNat = 2 * (2 * k + 1).toNat + 1 :=
          Gen11.usize_two_mul_add_one _ (by omega)
        have z : (0 : USize).toNat = (d - 1).toNat - 1 := by simp [hdp, hd2]
        have g00 := level_ge (level_child hl0 (by omega) _ (Or.inl e00) 0 z) (by simp)
        have g01 := level_ge (level_child hl0 (by omega) _ (Or.inr e01) 0 z) (by simp)
        have g10 := level_ge (level_child hl1 (by omega) _ (Or.inl e10) 0 z) (by simp)
        have g11 := level_ge (level_child hl1 (by omega) _ (Or.inr e11) 0 z) (by simp)
        have hkP' : k < P := hkP
        have h0P' : 2 * k < P := h0P
        have h1P' : 2 * k + 1 < P := h1P
        have n00 : ¬ 2 * (2 * k) < P := by intro h; have : (2 * (2 * k)).toNat < P.toNat := h; omega
        have n01 : ¬ 2 * (2 * k) + 1 < P := by
          intro h; have : (2 * (2 * k) + 1).toNat < P.toNat := h; omega
        have n10 : ¬ 2 * (2 * k + 1) < P := by
          intro h; have : (2 * (2 * k + 1)).toNat < P.toNat := h; omega
        have n11 : ¬ 2 * (2 * k + 1) + 1 < P := by
          intro h; have : (2 * (2 * k + 1) + 1).toNat < P.toNat := h; omega
        have hU : 4 * k.toNat + 3 < USize.size := by omega
        have f0 : 4 * k + 0 = 2 * (2 * k) := USize.toNat_inj.mp (by
          rw [four_mul_add_toNat 0 hU (by simp), e00, e2]; simp; omega)
        have f1 : 4 * k + 1 = 2 * (2 * k) + 1 := USize.toNat_inj.mp (by
          rw [four_mul_add_toNat 1 hU (by rw [usize_lit_toNat 1 (by omega)]; omega), e01, e2,
            usize_lit_toNat 1 (by omega)]; omega)
        have f2 : 4 * k + 2 = 2 * (2 * k + 1) := USize.toNat_inj.mp (by
          rw [four_mul_add_toNat 2 hU (by rw [usize_lit_toNat 2 (by omega)]; omega), e10, e21,
            usize_lit_toNat 2 (by omega)]; omega)
        have f3 : 4 * k + 3 = 2 * (2 * k + 1) + 1 := USize.toNat_inj.mp (by
          rw [four_mul_add_toNat 3 hU (by rw [usize_lit_toNat 3 (by omega)]; omega), e11, e21,
            usize_lit_toNat 3 (by omega)]; omega)
        rw [descend2, dite_eq_right h3, dite_eq_left hp]
        simp only []
        split
        · rename_i hx
          split
          · rename_i hy
            rw [descendW, dite_eq_left_of_eq_true (eq_true hkP')]
            simp only []
            rw [ite_eq_left hx, descendW, dite_eq_left_of_eq_true (eq_true h0P')]
            simp only []
            rw [ite_eq_left hy, descendW, dite_eq_right_iff.mpr (fun h => absurd h n00)]
            exact f0
          · rename_i hy
            rw [descendW, dite_eq_left_of_eq_true (eq_true hkP')]
            simp only []
            rw [ite_eq_left hx, descendW, dite_eq_left_of_eq_true (eq_true h0P')]
            simp only []
            rw [ite_eq_right hy, descendW, dite_eq_right_iff.mpr (fun h => absurd h n01)]
            exact f1
        · rename_i hx
          split
          · rename_i hy
            rw [descendW, dite_eq_left_of_eq_true (eq_true hkP')]
            simp only []
            rw [ite_eq_right hx, descendW, dite_eq_left_of_eq_true (eq_true h1P')]
            simp only []
            rw [ite_eq_left hy, descendW, dite_eq_right_iff.mpr (fun h => absurd h n10)]
            exact f2
          · rename_i hy
            rw [descendW, dite_eq_left_of_eq_true (eq_true hkP')]
            simp only []
            rw [ite_eq_right hx, descendW, dite_eq_left_of_eq_true (eq_true h1P')]
            simp only []
            rw [ite_eq_right hy, descendW, dite_eq_right_iff.mpr (fun h => absurd h n11)]
            exact f3
      · by_cases h1 : d = 1
        · have hd1 : d.toNat = 1 := by
            rw [h1]; rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
          have hkP := level_lt hk (by omega)
          have e2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
          have e21 : (2 * k + 1).toNat = 2 * k.toNat + 1 :=
            Gen11.usize_two_mul_add_one k (by omega)
          have hdp : (d - 1).toNat = 0 := by
            rw [Gen16.pred_toNat d (by intro h; rw [h] at hd1; simp at hd1)]; omega
          have hl0 : Level P (d - 1) (2 * k) :=
            level_child hk (by omega) _ (Or.inl e2) _ (by omega)
          have hl1 : Level P (d - 1) (2 * k + 1) :=
            level_child hk (by omega) _ (Or.inr e21) _ (by omega)
          have g0 := level_ge hl0 hdp
          have g1 := level_ge hl1 hdp
          have hkP' : k < P := hkP
          have n0 : ¬ 2 * k < P := by intro h; have : (2 * k).toNat < P.toNat := h; omega
          have n1 : ¬ 2 * k + 1 < P := by
            intro h; have : (2 * k + 1).toNat < P.toNat := h; omega
          rw [descend2, dite_eq_right h3, dite_eq_right hp, dite_eq_left h1, descendW,
            dite_eq_left_of_eq_true (eq_true hkP')]
          simp only []
          split
          · rw [descendW, dite_eq_right_iff.mpr (fun h => absurd h n0)]
          · rw [descendW, dite_eq_right_iff.mpr (fun h => absurd h n1)]
        · have hd0 : d.toNat = 0 := by
            have : ¬ 3 ≤ d.toNat := fun h => h3 ((USize.le_iff_toNat_le).mpr (by
              rw [three_toNat]; exact h))
            have : d.toNat ≠ 2 := fun h => hp (USize.toNat_inj.mp (by rw [h, two_toNat]))
            have : d.toNat ≠ 1 := fun h => h1 (USize.toNat_inj.mp (by
              rw [h]; rcases USize.size_eq with h' | h' <;> simp [USize.toNat_ofNat, h']))
            omega
          have g := level_ge hk hd0
          have nk : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
          rw [descend2, dite_eq_right h3, dite_eq_right hp, dite_eq_right h1, descendW,
            dite_eq_right_iff.mpr (fun h => absurd h nk)]

/-! ## The driver -/

/-- Generation 23's driver with the descent ending in a branch-free pair of levels. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Compiled) (msN : Array Nat) (n : Nat)
    (hms : msN.size = n) (hval : Gen15.ValidChanges C n) (nW : USize) (numRx : USize) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Bounds W nW P numRx rates) (hL : Level P D 1) (rxs : Array RxW)
    (hR : RxOK W rates numRx.toNat rxs)
    (horizon : Float) (save : Bool) (cap : USize)
    (evFuel prFuel : USize) (pop : FloatArray) (hpop : pop.size = nW.toNat + 1) (c : CacheV)
    (hc : Sized nW P c) (now total elapsed : Float) (s0 s1 s2 s3 : UInt64) (count : USize)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  if _hz : prFuel = 0 then .error .proposalLimit
  else
    have hP1 := hB.leaves
    have htree : 2 * P.toNat ≤ c.tree.size := Nat.le_of_eq hc.2.2.symm
    let rng : Xoshiro := ⟨s0, s1, s2, s3⟩
    let (u, rng) := rng.uniform
    if !decide (floatZero ≤ u) then .error .invalidUniform
    else if !decide (u < floatOne) then .error .invalidUniform
    else
      let (e, rng) := rng.exponential
      if !decide (e < floatInf) then .error .invalidExponential
      else if !decide (floatZero < e) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !decide (elapsed < floatInf) then .error .invalidTime
        else if !decide (floatNegInf < elapsed) then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !decide (floatZero ≤ v) then .error .invalidUniform
          else if !decide (v < floatOne) then .error .invalidUniform
          else
            let k := if 9 ≤ D then descend2 c.tree P htree hP2 D 1 hL (u * total)
              else descendW c.tree P htree hP2 1 Gen11.usize_one_pos (u * total)
            have hk : k.toNat < 2 * P.toNat := by
              have hw := descendW_lt c.tree P htree hP2 _ 1 Gen11.usize_one_pos (u * total)
                (Nat.le_refl _) (by rw [one_toNat]; omega)
              simp only [k]
              split
              · rw [descend2_eq c.tree P htree hP2 _ D 1 hL Gen11.usize_one_pos (u * total) (Nat.le_refl _)]
                exact hw
              · exact hw
            let j := k - P
            if hacc : (if hj : j < numRx then
                have hjn : j.toNat < numRx.toNat := hj
                have hjr : j.toNat < rxs.size := by have := hR.size; omega
                let r := rxs.uget j hjr
                have hst : r.s.toNat < nW.toNat ∧ r.t.toNat < nW.toNat :=
                  (hR.get j.toNat hjr hjn).factorBounds hB hjn
                let threshold := v * c.tree.uget k (by omega)
                let actual := r.rate * evalR r pop (by omega) (by omega)
                decide (floatZero < actual) && decide (threshold ≤ actual)
              else false) = true then
              have hj : j < numRx := by
                by_cases hn : j < numRx
                · exact hn
                · rw [dite_eq_right hn] at hacc; exact absurd hacc Bool.false_ne_true
              let time := now + elapsed / total
              if !decide (time < floatInf) then .error .invalidTime
              else if !decide (floatNegInf < time) then .error .invalidTime
              else if !decide (now ≤ time) then .error .invalidTime
              else if !decide (time ≤ horizon) then
                let st : State := ⟨ofCounts pop n, ofCounts c.lo n, ofCounts c.hi n⟩
                .ok ⟨st, horizon, count.toNat, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                  trace.push (horizon, st)⟩
              else if he : evFuel = 0 then .error .eventLimit
              else
                have hjn : j.toNat < numRx.toNat := hj
                have hjr : j.toNat < rxs.size := by have := hR.size; omega
                let r := rxs.uget j hjr
                have hcb : r.c0.toNat < nW.toNat ∧ r.c1.toNat < nW.toNat ∧
                    (r.three = true → r.c2.toNat < nW.toNat) :=
                  (hR.get j.toNat hjr hjn).changeBounds hB hjn
                let p := applyR r nW hcb.1 hcb.2.1 hcb.2.2 W.ms c.lo c.hi hB.ms
                  (Nat.le_of_eq hc.1.symm) (Nat.le_of_eq hc.2.1.symm) pop (by omega)
                have hp : p.size = nW.toNat + 1 := by rw [applyR_size]; exact hpop
                if p.uget nW (by omega) == floatZero then
                  let trace := if save then trace.push (time, ⟨ofCounts p n, ofCounts c.lo n,
                    ofCounts c.hi n⟩) else trace
                  run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
                    (evFuel - 1) cap p hp c hc time total floatZero rng.s0 rng.s1 rng.s2 rng.s3
                    (count + 1) trace
                else if smallR r p (by omega) (by omega)
                    (fun h => by have := hcb.2.2 h; omega) then
                  let c' := refreshFromR W P hP2 D nW numRx rates hB r hcb.1 hcb.2.1
                    hcb.2.2 p (by omega) c hc
                  have hc' : Sized nW P c' := refreshFromR_sized W P hP2 D nW numRx rates hB r
                    hcb.1 hcb.2.1 hcb.2.2 p (by omega) c hc
                  let trace := if save then trace.push (time, ⟨ofCounts p n, ofCounts c'.lo n,
                    ofCounts c'.hi n⟩) else trace
                  let total := c'.tree.uget 1 (by
                    have := hc'.2.2
                    rw [one_toNat]
                    omega)
                  if !decide (total < floatInf) then .error (.invalidRate numRx.toNat)
                  else if !decide (floatNegInf < total) then .error (.invalidRate numRx.toNat)
                  else if !decide (floatZero < total) then
                    let st : State := ⟨ofCounts p n, ofCounts c'.lo n, ofCounts c'.hi n⟩
                    .ok ⟨st, horizon, count.toNat + 1, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                      trace.push (horizon, st)⟩
                  else
                    run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save
                      cap (evFuel - 1) cap p hp c' hc' time total floatZero rng.s0 rng.s1 rng.s2
                      rng.s3 (count + 1) trace
                else
                  -- a count reached `2^25`: generation 17's refresh, then generation 17
                  let popN := ofCounts p n
                  if hpN : popN.size = n then
                    let cN := toCache C n c
                    let chsN := C.changes[j.toNat]!
                    let c' := chsN.foldl
                      (fun c ch => Gen16.refresh C.gen5 codes P hP2 msN popN c ch.species) cN
                    let trace := if save then trace.push (time, ⟨popN, c'.lo, c'.hi⟩) else trace
                    let total := Gen17.fget c'.tree 1
                    if !decide (total < floatInf) then .error (.invalidRate numRx.toNat)
                    else if !decide (floatNegInf < total) then .error (.invalidRate numRx.toNat)
                    else if !decide (floatZero < total) then
                      .ok ⟨⟨popN, c'.lo, c'.hi⟩, horizon, count.toNat + 1,
                        ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩, trace.push (horizon, ⟨popN, c'.lo, c'.hi⟩)⟩
                    else if hs : c'.lo.size = n ∧ c'.hi.size = n then
                      Gen17.run C codes msN n hms hval numRx P hP2 C.gen5.base.rates
                        C.gen5.base.factors horizon save cap (evFuel - 1) cap popN hpN c' hs.1 hs.2
                        time total floatZero rng.s0 rng.s1 rng.s2 rng.s3 (count + 1) trace
                    else .error .invalidShape
                  else .error .invalidShape
            else
              run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
                evFuel (prFuel - 1) pop hpop c hc now total elapsed rng.s0 rng.s1 rng.s2 rng.s3
                count trace
termination_by (evFuel.toNat, prFuel.toNat)
decreasing_by
  all_goals first
    | (have : evFuel.toNat ≠ 0 := fun h => he (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat evFuel he]; exact Prod.Lex.left _ _ (by omega))
    | (have : prFuel.toNat ≠ 0 := fun h => _hz (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat prFuel _hz]; exact Prod.Lex.right _ (by omega))

/-- Generation 23's start, entering generation 24's driver. -/
def start (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let n := C.gen5.base.ms.size
  let total := c.tree.get! 1
  let W := compileW C codes
  let popW := (toCounts pop).push 0
  let cV : CacheV := ⟨toCounts c.lo, toCounts c.hi, c.tree⟩
  if h : Gen7.finite total = true ∧ decide (floatZero < total) = true ∧
      2 * C.gen5.base.leaves < USize.size then
    if hs : (pop.size = n ∧ c.lo.size = n ∧ c.hi.size = n ∧ Gen15.validChanges C n = true ∧
        Gen17.changesOK C = true ∧ Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
        count + fuel < USize.size ∧ cap < USize.size ∧ C.gen5.base.numRx < USize.size ∧
        n + 1 < USize.size ∧ allSmall pop = true ∧ allSmall c.lo = true ∧ allSmall c.hi = true ∧
        allSmall C.gen5.base.ms = true ∧
        C.gen5.base.factors.all (Gen18.FactorW.ok n) = true ∧
        codes.all (·.all fun c => c == 0 || c == 1 || (c % 4 == 0 && decide (4 ≤ c) &&
          decide (c / 4 ≤ n))) = true ∧
        codes.size = n ∧ C.gen5.depRates.size = n ∧ C.gen5.base.deps.size = n ∧
        (List.range n).all (fun s => (codes[s]!).size == (C.gen5.base.deps[s]!).size &&
          (C.gen5.depRates[s]!).size == (C.gen5.base.deps[s]!).size &&
          decide ((C.gen5.base.deps[s]!).size < USize.size) &&
          (C.gen5.base.deps[s]!).all (· < C.gen5.base.leaves)) = true ∧
        C.changes.all (·.all fun ch => decide (ch.up < 67108864) && decide (ch.down < 67108864))
          = true ∧
        C.gen5.base.rates.data.all (fun r => decide (floatZero ≤ r) && decide (r < rateMax))
          = true) ∧
        boundsOK W n.toUSize C.gen5.base.leaves.toUSize C.gen5.base.numRx.toUSize
          C.gen5.base.rates = true ∧
        popW.size = n.toUSize.toNat + 1 ∧ cV.lo.size = n.toUSize.toNat ∧
        cV.hi.size = n.toUSize.toNat ∧ cV.tree.size = 2 * C.gen5.base.leaves.toUSize.toNat ∧
        W.changes.all (fun chs => chs.size == 2 || chs.size == 3) = true ∧
        C.gen5.base.leaves.toUSize.toNat = 2 ^ C.gen5.base.depth.toUSize.toNat then
      have hB := boundsOK_spec hs.2.1
      have hnum : C.gen5.base.numRx.toUSize.toNat = C.gen5.base.numRx := by
        rw [Nat.toUSize, USize.toNat_ofNat_of_lt' hs.1.2.2.2.2.2.2.2.2.1]
      run C codes W C.gen5.base.ms n rfl (Gen15.validChanges_spec hs.1.2.2.2.1) n.toUSize
        C.gen5.base.numRx.toUSize C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h.2.2)
        C.gen5.base.depth.toUSize C.gen5.base.rates hB (level_root hs.2.2.2.2.2.2.2)
        (buildRx W C.gen5.base.rates C.gen5.base.numRx)
        (by
          rw [hnum]
          exact buildRx_ok W C.gen5.base.rates C.gen5.base.numRx
            (by have := hB.changes; omega) hs.2.2.2.2.2.2.1)
        horizon save cap.toUSize fuel.toUSize cap.toUSize popW hs.2.2.1 cV
        ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩
        now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize trace
    else Gen23.start C codes horizon save cap fuel pop c now rng count trace
  else Gen23.start C codes horizon save cap fuel pop c now rng count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(Gen7.finite start && Gen7.finite horizon && decide (start ≤ horizon)) then
    .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen6.compile net
    Gen24.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen24
