import JumpProcessesLean.TreeRSSA.Gen25

/-!
# Tree-RSSA, generation 26: reactions with one change take the fast path

Generations 21 to 25 keep a record of two or three changes per reaction, and their start runs
generation 20 on a network with a reaction of one change, such as a creation `∅ → A`, a
degradation `A → ∅` or an autocatalysis `A → 2A`. Generation 26's record (`RxV`) holds one, two or
three changes; its firing, small-count test and refresh take the second change only if the
reaction has one. The rest is generation 25's.
-/

namespace JumpProcessesLean.TreeRSSA.Gen26

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)
open Gen18 (ChangeW DepW Compiled compileW staleW bracketLo bracketHi ff2 ofCounts toCounts
  allSmall twoPow25)
open Gen19 (CacheV toCache rateMax)
open Gen20 (Bounds boundsOK boundsOK_spec Sized size_uset one_toNat)
open Gen22 (Level level_lt level_ge level_two_mul_lt level_child two_toNat two_le_toNat
  toNat_sub_two level_root)
open Gen25 (stateOfV toCacheV apply1C)

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

/-! ## Records -/

/-- A reaction's rate, its factor (`kind`, `s`, `t` as in `FactorW`) and its one, two or three
changes: `(c0, add0, a0)`, then `(c1, add1, a1)` unless `one`, then `(c2, add2, a2)` if `three`. -/
structure RxV where
  s : USize
  t : USize
  c0 : USize
  c1 : USize
  c2 : USize
  rate : Float
  a0 : Float
  a1 : Float
  a2 : Float
  kind : UInt64
  one : Bool
  three : Bool
  add0 : Bool
  add1 : Bool
  add2 : Bool
  deriving Inhabited

/-- Reaction `j`'s record. -/
def rxOfV (W : Compiled) (rates : FloatArray) (j : Nat) : RxV :=
  let f := W.factors[j]!
  let chs := W.changes[j]!
  let ch0 := chs.getD 0 Gen21.noChange
  let ch1 := chs.getD 1 Gen21.noChange
  let ch2 := chs.getD 2 Gen21.noChange
  { s := f.s, t := f.t, c0 := ch0.species, c1 := ch1.species, c2 := ch2.species,
    rate := rates.get! j, a0 := ch0.amount, a1 := ch1.amount, a2 := ch2.amount, kind := f.kind,
    one := chs.size == 1, three := chs.size == 3, add0 := ch0.add, add1 := ch1.add,
    add2 := ch2.add }

/-- The records of reactions `0, …, m - 1`. -/
def buildRxV (W : Compiled) (rates : FloatArray) (m : Nat) : Array RxV :=
  (Array.range m).map (rxOfV W rates)

/-- Record `r` holds reaction `j`: its rate, its factor and its one, two or three changes. -/
structure RxAtV (W : Compiled) (rates : FloatArray) (j : Nat) (r : RxV) : Prop where
  rate : r.rate = rates.get! j
  kind : r.kind = (W.factors[j]!).kind
  s : r.s = (W.factors[j]!).s
  t : r.t = (W.factors[j]!).t
  size : (W.changes[j]!).size = if r.one then 1 else if r.three then 3 else 2
  onethree : r.one = true → r.three = false
  ch0 : (W.changes[j]!)[0]! = ⟨r.c0, r.add0, r.a0⟩
  ch1 : r.one = false → (W.changes[j]!)[1]! = ⟨r.c1, r.add1, r.a1⟩
  ch2 : r.three = true → (W.changes[j]!)[2]! = ⟨r.c2, r.add2, r.a2⟩

/-- The records hold reactions `0, …, m - 1`. -/
structure RxOKV (W : Compiled) (rates : FloatArray) (m : Nat) (rxs : Array RxV) : Prop where
  size : rxs.size = m
  get : ∀ j (h : j < rxs.size), j < m → RxAtV W rates j rxs[j]

theorem rxOfV_at (W : Compiled) (rates : FloatArray) (j : Nat) (hj : j < W.changes.size)
    (h13 : (W.changes[j]).size = 1 ∨ (W.changes[j]).size = 2 ∨ (W.changes[j]).size = 3) :
    RxAtV W rates j (rxOfV W rates j) := by
  have e : W.changes[j]! = W.changes[j] := getElem!_pos W.changes j hj
  have hs : 1 ≤ (W.changes[j]).size := by omega
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [rxOfV, e]
    rcases h13 with h | h | h <;> simp [h]
  · intro h1
    simp only [rxOfV, e, beq_iff_eq] at h1 ⊢
    simp [h1]
  · simp only [rxOfV, e, Array.getD, dite_eq_left (show 0 < (W.changes[j]).size by omega)]
    exact getElem!_pos _ 0 (by omega)
  · intro h1
    have h1' : (W.changes[j]).size ≠ 1 := by
      intro hh
      simp [rxOfV, e, hh] at h1
    simp only [rxOfV, e, Array.getD, dite_eq_left (show 1 < (W.changes[j]).size by omega)]
    exact getElem!_pos _ 1 (by omega)
  · intro h3
    have h3' : (W.changes[j]).size = 3 := by
      simp only [rxOfV, e, beq_iff_eq] at h3; exact h3
    simp only [rxOfV, e, Array.getD, dite_eq_left (show 2 < (W.changes[j]).size by omega)]
    exact getElem!_pos _ 2 (by omega)

theorem buildRxV_ok (W : Compiled) (rates : FloatArray) (m : Nat) (hm : m ≤ W.changes.size)
    (h13 : W.changes.all (fun chs => chs.size == 1 || chs.size == 2 || chs.size == 3) = true) :
    RxOKV W rates m (buildRxV W rates m) := by
  refine ⟨by simp [buildRxV], fun j h hj => ?_⟩
  have hc : j < W.changes.size := by omega
  have e : (buildRxV W rates m)[j] = rxOfV W rates j := by simp [buildRxV]
  rw [e]
  refine rxOfV_at W rates j hc ?_
  rw [Array.all_eq_true] at h13
  have := h13 j hc
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The factor's species of a record are in range. -/
theorem RxAtV.factorBounds {W : Compiled} {rates : FloatArray} {j : Nat} {r : RxV}
    {nW P numRx : USize} (hB : Bounds W nW P numRx rates) (hj : j < numRx.toNat)
    (h : RxAtV W rates j r) : r.s.toNat < nW.toNat ∧ r.t.toNat < nW.toNat := by
  have hf : j < W.factors.size := by have := hB.factors; omega
  rw [h.s, h.t, getElem!_pos W.factors j hf]
  exact hB.factorST j hf

/-- The changed species of a record are in range. -/
theorem RxAtV.changeBounds {W : Compiled} {rates : FloatArray} {j : Nat} {r : RxV}
    {nW P numRx : USize} (hB : Bounds W nW P numRx rates) (hj : j < numRx.toNat)
    (h : RxAtV W rates j r) :
    r.c0.toNat < nW.toNat ∧ (r.one = false → r.c1.toNat < nW.toNat) ∧
      (r.three = true → r.c2.toNat < nW.toNat) := by
  have hc : j < W.changes.size := by have := hB.changes; omega
  have e : W.changes[j]! = W.changes[j] := getElem!_pos W.changes j hc
  have hsz := h.size
  rw [e] at hsz
  have hs1 : 1 ≤ (W.changes[j]).size := by
    rw [hsz]; split
    · exact Nat.le_refl 1
    · split <;> omega
  refine ⟨?_, fun h1 => ?_, fun h3 => ?_⟩
  · have e0 := h.ch0
    rw [e, getElem!_pos _ 0 (by omega)] at e0
    have := hB.changeS j hc 0 (by omega)
    rw [e0] at this
    exact this
  · have hs2 : 2 ≤ (W.changes[j]).size := by
      rw [hsz, ite_eq_right (by simp [h1])]; split <;> omega
    have e1 := h.ch1 h1
    rw [e, getElem!_pos _ 1 (by omega)] at e1
    have := hB.changeS j hc 1 (by omega)
    rw [e1] at this
    exact this
  · have h1 : r.one = false := by
      cases h1 : r.one
      · rfl
      · have := h.onethree h1; rw [h3] at this; exact absurd this (by decide)
    have hs3 : 3 ≤ (W.changes[j]).size := by
      rw [hsz, ite_eq_right (by simp [h1]), ite_eq_left h3]; exact Nat.le_refl 3
    have e2 := h.ch2 h3
    rw [e, getElem!_pos _ 2 (by omega)] at e2
    have := hB.changeS j hc 2 (by omega)
    rw [e2] at this
    exact this

/-- The factor of a record at the counts. -/
@[inline] def evalV (r : RxV) (pop : FloatArray) (hs : r.s.toNat < pop.size)
    (ht : r.t.toNat < pop.size) : Float :=
  let x := pop.uget r.s hs
  if r.kind = 0 then x else if r.kind = 1 then ff2 x else x * pop.uget r.t ht

/-! ## Firing -/

/-- Generation 25's `applyRC` on a record of one, two or three changes. -/
@[inline] def applyRV (r : RxV) (nW : USize) (h0 : r.c0.toNat < nW.toNat)
    (h1 : r.one = false → r.c1.toNat < nW.toNat) (h2 : r.three = true → r.c2.toNat < nW.toNat)
    (ms : FloatArray) (c : CacheV) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ c.lo.size)
    (hhi : nW.toNat ≤ c.hi.size) (pop : FloatArray) (hpop : nW.toNat < pop.size) : FloatArray :=
  let (⟨p0, e0⟩, st0) := apply1C r.c0 r.add0 r.a0 ms c nW h0 hms hlo hhi pop hpop false
  if h1' : r.one = true then p0.uset nW (if st0 then floatOne else floatZero) (by omega)
  else
    let (⟨p1, e1⟩, st1) :=
      apply1C r.c1 r.add1 r.a1 ms c nW (h1 (by simpa using h1')) hms hlo hhi p0 (by omega) st0
    if h : r.three = true then
      let (⟨p2, e2⟩, st2) :=
        apply1C r.c2 r.add2 r.a2 ms c nW (h2 h) hms hlo hhi p1 (by omega) st1
      p2.uset nW (if st2 then floatOne else floatZero) (by omega)
    else p1.uset nW (if st1 then floatOne else floatZero) (by omega)

theorem applyRV_size (r : RxV) (nW : USize) (h0 : r.c0.toNat < nW.toNat)
    (h1 : r.one = false → r.c1.toNat < nW.toNat) (h2 : r.three = true → r.c2.toNat < nW.toNat)
    (ms : FloatArray) (c : CacheV) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ c.lo.size)
    (hhi : nW.toNat ≤ c.hi.size) (pop : FloatArray) (hpop : nW.toNat < pop.size) :
    (applyRV r nW h0 h1 h2 ms c hms hlo hhi pop hpop).size = pop.size := by
  simp only [applyRV]
  split
  · rw [size_uset]
    exact (apply1C _ _ _ _ _ _ _ _ _ _ _ _ _).1.property
  · split
    · rw [size_uset]
      exact (apply1C _ _ _ _ _ _ _ _ _ _ _ _ _).1.property.trans
        ((apply1C _ _ _ _ _ _ _ _ _ _ _ _ _).1.property.trans
          (apply1C _ _ _ _ _ _ _ _ _ _ _ _ _).1.property)
    · rw [size_uset]
      exact (apply1C _ _ _ _ _ _ _ _ _ _ _ _ _).1.property.trans
        (apply1C _ _ _ _ _ _ _ _ _ _ _ _ _).1.property

/-- Whether the changed counts are below `2^25`, for a record of one, two or three changes. -/
@[inline] def smallV (r : RxV) (pop : FloatArray) (h0 : r.c0.toNat < pop.size)
    (h1 : r.one = false → r.c1.toNat < pop.size) (h2 : r.three = true → r.c2.toNat < pop.size) :
    Bool :=
  if pop.uget r.c0 h0 < twoPow25 then
    if h1' : r.one = true then true
    else if pop.uget r.c1 (h1 (by simpa using h1')) < twoPow25 then
      if h : r.three = true then
        if pop.uget r.c2 (h2 h) < twoPow25 then true else false
      else true
    else false
  else false

/-! ## Refreshes -/

/-- Generation 16's `fixUntilGo`, compiled in this module so that the refreshes inline it. -/
def fixUntilR (P : USize) (n : USize) (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size)
    (node : USize) (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float) : FloatArray :=
  if hz : n = 0 then tree
  else
    let k := node >>> 1
    let o := other >>> 1
    if k = o then tree
    else
      have hs : (node ^^^ 1).toNat < tree.size := by rw [Gen12.xor_one_toNat]; omega
      have hk : k.toNat < tree.size := by rw [Gen12.shiftRight_one_toNat]; omega
      let v := v + tree.uget (node ^^^ 1) hs
      fixUntilR P (n - 1) (tree.uset k v hk) (by rw [Gen12.size_uset]; exact hP) k
        (by rw [Gen12.shiftRight_one_toNat]; omega) o v
termination_by n.toNat
decreasing_by rw [Gen16.pred_toNat n hz]; have : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp (by rw [h]; rfl)); omega

/-- `Gen12.fixPathR` with the level count in a machine word. -/
def fixPathR (P : USize) (n : USize) (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size)
    (node : USize) (hn : node.toNat < 2 * P.toNat) (v : Float) : FloatArray :=
  if hz : n = 0 then tree
  else
    let k := node >>> 1
    have hs : (node ^^^ 1).toNat < tree.size := by rw [Gen12.xor_one_toNat]; omega
    have hk : k.toNat < tree.size := by rw [Gen12.shiftRight_one_toNat]; omega
    let v := v + tree.uget (node ^^^ 1) hs
    fixPathR P (n - 1) (tree.uset k v hk) (by rw [Gen12.size_uset]; exact hP) k
      (by rw [Gen12.shiftRight_one_toNat]; omega) v
termination_by n.toNat
decreasing_by rw [Gen16.pred_toNat n hz]; have : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp (by rw [h]; rfl)); omega

theorem fixUntilR_size (P : USize) : ∀ (m : Nat) (n : USize), n.toNat = m →
    ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float),
      (fixUntilR P n tree hP node hn other v).size = tree.size := by
  intro m
  induction m with
  | zero =>
    intro n hm tree hP node hn other v
    have hz : n = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [fixUntilR, dite_eq_left hz]
  | succ m ih =>
    intro n hm tree hP node hn other v
    have hz : n ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [fixUntilR, dite_eq_right hz]
    dsimp only
    split
    · rfl
    · rw [ih _ (by rw [Gen16.pred_toNat n hz]; omega), Gen12.size_uset]

theorem fixPathR_size (P : USize) : ∀ (m : Nat) (n : USize), n.toNat = m →
    ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (v : Float),
      (fixPathR P n tree hP node hn v).size = tree.size := by
  intro m
  induction m with
  | zero =>
    intro n hm tree hP node hn v
    have hz : n = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [fixPathR, dite_eq_left hz]
  | succ m ih =>
    intro n hm tree hP node hn v
    have hz : n ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [fixPathR, dite_eq_right hz]
    dsimp only
    rw [ih _ (by rw [Gen16.pred_toNat n hz]; omega), Gen12.size_uset]

/-- Generation 21's `setBoundsR` through this module's walks. -/
def setBoundsR (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (nW : USize)
    (hi : FloatArray) (hhi : nW.toNat ≤ hi.size) (h0 h1 g0 g1 : Float) (ds : Array DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat)
    (i : USize) (tree : FloatArray) (htree : 2 * P.toNat ≤ tree.size) (pending : USize)
    (hpend : pending = 0 ∨ pending.toNat < 2 * P.toNat) : FloatArray :=
  if h : i < ds.usize then
    have hi' := Gen15.lt_size_of_lt_usize ds i h
    let d := ds.uget i hi'
    have hd : d.k.toNat < P.toNat ∧ d.partner.toNat ≤ nW.toNat := hds i.toNat hi'
    let pH := if hp : d.partner = 0 then floatOne
      else hi.uget (d.partner - 1) (by
        have : d.partner.toNat ≠ 0 := fun h0 => hp (USize.toNat_inj.mp (by rw [h0]; rfl))
        rw [Gen20.usize_sub_one_toNat hp]; omega)
    let bN := if d.two then h1 else h0
    if bN == (if d.two then g1 else g0) then
      setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds (i + 1) tree htree pending hpend
    else if pH == floatZero then
      setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds (i + 1) tree htree pending hpend
    else
      let leaf := P + d.k
      have hleaf : leaf.toNat = P.toNat + d.k.toNat := by
        have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hpend' : pending ≠ 0 → pending.toNat < 2 * P.toNat := fun hz => hpend.resolve_left hz
      let tree' := if hz : pending = 0 then tree
        else fixUntilR P D tree htree pending (hpend' hz) leaf
          (tree.uget pending (by have := hpend' hz; omega))
      have htree' : 2 * P.toNat ≤ tree'.size := by
        simp only [tree']
        split
        · exact htree
        · rw [fixUntilR_size P _ D rfl]; exact htree
      setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds (i + 1)
        (tree'.uset leaf (d.rate * (bN * pH)) (by omega)) (by rw [size_uset]; exact htree') leaf
        (Or.inr (by omega))
  else if hz : pending = 0 then tree
    else fixPathR P D tree htree pending (hpend.resolve_left hz)
      (tree.uget pending (by have := hpend.resolve_left hz; omega))
termination_by ds.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize ds i h]; omega)

theorem setBoundsR_size (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (nW : USize)
    (hi : FloatArray) (hhi : nW.toNat ≤ hi.size) (h0 h1 g0 g1 : Float) (ds : Array DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat) :
    ∀ m (i : USize), ds.size - i.toNat = m → ∀ (tree : FloatArray)
      (htree : 2 * P.toNat ≤ tree.size) (pending : USize) hpend,
      (setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend).size =
        tree.size := by
  intro m
  induction m with
  | zero =>
    intro i hm tree htree pending hpend
    have hge : ¬ i < ds.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize ds i h; omega
    rw [setBoundsR, dite_eq_right hge]
    split
    · rfl
    · rw [fixPathR_size P _ D rfl]
  | succ m ih =>
    intro i hm tree htree pending hpend
    by_cases h : i < ds.usize
    · have hs := Gen15.succ_toNat_of_lt_usize ds i h
      rw [setBoundsR, dite_eq_left h]
      dsimp only
      repeat' split
      all_goals first
        | exact ih (i + 1) (by omega) _ _ _ _
        | (rw [ih (i + 1) (by omega), size_uset, fixUntilR_size P _ D rfl])
        | (rw [ih (i + 1) (by omega), size_uset])
    · rw [setBoundsR, dite_eq_right h]
      split
      · rfl
      · rw [fixPathR_size P _ D rfl]

/-- Generation 20's `rebracketU` through this module's `setBoundsR`. -/
@[inline] def rebracketR (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (c : CacheV) (hc : Sized nW P c) (s : USize)
    (hs : s.toNat < nW.toNat) : CacheV :=
  have hms := hB.ms
  have hdeps := hB.deps
  let x := (pop.uget s (by omega)).toUInt64
  let m := (W.ms.uget s (by omega)).toUInt64
  let hiS := c.hi.uget s (by have := hc.2.1; omega)
  let loN := (bracketLo m x).toFloat
  let hiN := (bracketHi m x).toFloat
  let lo := c.lo.uset s loN (by have := hc.1; omega)
  let hi := c.hi.uset s hiN (by have := hc.2.1; omega)
  ⟨lo, hi, setBoundsR P hP2 D nW hi (by rw [size_uset]; exact Nat.le_of_eq hc.2.1.symm) hiN (ff2 hiN) hiS (ff2 hiS)
    (W.deps.uget s (by omega)) (fun k h => hB.depKP s.toNat (by omega) k h) 0 c.tree
    (Nat.le_of_eq hc.2.2.symm) 0 (Or.inl rfl)⟩

theorem rebracketR_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (c : CacheV) (hc : Sized nW P c) (s : USize)
    (hs : s.toNat < nW.toNat) :
    Sized nW P (rebracketR W P hP2 D nW numRx rates hB pop hpop c hc s hs) := by
  refine ⟨?_, ?_, ?_⟩
  · show (c.lo.uset _ _ _).size = nW.toNat
    rw [size_uset]; exact hc.1
  · show (c.hi.uset _ _ _).size = nW.toNat
    rw [size_uset]; exact hc.2.1
  · show (setBoundsR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).size = 2 * P.toNat
    rw [setBoundsR_size _ _ _ _ _ _ _ _ _ _ _ _ _ 0 rfl]
    exact hc.2.2


/-- Rebracket species `s` if it left its bracket: one step of generation 20's
`refreshFromU`. -/
@[inline] def refresh1 (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (s : USize) (hs : s.toNat < nW.toNat) (c : CacheV)
    (hc : Sized nW P c) : CacheV :=
  have hms := hB.ms
  if staleW (W.ms.uget s (by omega)) (pop.uget s (by omega))
      (c.lo.uget s (by have := hc.1; omega)) (c.hi.uget s (by have := hc.2.1; omega)) then
    rebracketR W P hP2 D nW numRx rates hB pop hpop c hc s hs
  else c

theorem refresh1_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (s : USize) (hs : s.toNat < nW.toNat) (c : CacheV)
    (hc : Sized nW P c) :
    Sized nW P (refresh1 W P hP2 D nW numRx rates hB pop hpop s hs c hc) := by
  simp only [refresh1]
  split
  · exact rebracketR_sized W P hP2 D nW numRx rates hB pop hpop c hc s hs
  · exact hc

/-- Generation 22's `refreshFromR` on a record of one, two or three changes. -/
def refreshFromRV (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (r : RxV)
    (h0 : r.c0.toNat < nW.toNat) (h1 : r.one = false → r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (c : CacheV) (hc : Sized nW P c) : CacheV :=
  let c0 := refresh1 W P hP2 D nW numRx rates hB pop hpop r.c0 h0 c hc
  have e0 := refresh1_sized W P hP2 D nW numRx rates hB pop hpop r.c0 h0 c hc
  if h1' : r.one = true then c0
  else
    have h1'' : r.c1.toNat < nW.toNat := h1 (by simpa using h1')
    let c1 := refresh1 W P hP2 D nW numRx rates hB pop hpop r.c1 h1'' c0 e0
    have e1 := refresh1_sized W P hP2 D nW numRx rates hB pop hpop r.c1 h1'' c0 e0
    if h : r.three = true then refresh1 W P hP2 D nW numRx rates hB pop hpop r.c2 (h2 h) c1 e1
    else c1

theorem refreshFromRV_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates)
    (r : RxV) (h0 : r.c0.toNat < nW.toNat) (h1 : r.one = false → r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (c : CacheV) (hc : Sized nW P c) :
    Sized nW P (refreshFromRV W P hP2 D nW numRx rates hB r h0 h1 h2 pop hpop c hc) := by
  simp only [refreshFromRV]
  split
  · exact refresh1_sized _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · split
    · exact refresh1_sized _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · exact refresh1_sized _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## The driver -/

/-- Generation 25's driver on records of one, two or three changes. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Compiled) (msN : Array Nat) (n : Nat)
    (hms : msN.size = n) (hval : Gen15.ValidChanges C n) (nW : USize) (numRx : USize) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Bounds W nW P numRx rates) (hL : Level P D 1) (rxs : Array RxV)
    (hR : RxOKV W rates numRx.toNat rxs)
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
                let actual := r.rate * evalV r pop (by omega) (by omega)
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
                let st : State := stateOfV pop c n
                .ok ⟨st, horizon, count.toNat, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                  trace.push (horizon, st)⟩
              else if he : evFuel = 0 then .error .eventLimit
              else
                have hjn : j.toNat < numRx.toNat := hj
                have hjr : j.toNat < rxs.size := by have := hR.size; omega
                let r := rxs.uget j hjr
                have hcb : r.c0.toNat < nW.toNat ∧ (r.one = false → r.c1.toNat < nW.toNat) ∧
                    (r.three = true → r.c2.toNat < nW.toNat) :=
                  (hR.get j.toNat hjr hjn).changeBounds hB hjn
                let p := applyRV r nW hcb.1 hcb.2.1 hcb.2.2 W.ms c hB.ms
                  (Nat.le_of_eq hc.1.symm) (Nat.le_of_eq hc.2.1.symm) pop (by omega)
                have hp : p.size = nW.toNat + 1 := by rw [applyRV_size]; exact hpop
                if p.uget nW (by omega) == floatZero then
                  let trace := if save then trace.push (time, stateOfV p c n) else trace
                  run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
                    (evFuel - 1) cap p hp c hc time total floatZero rng.s0 rng.s1 rng.s2 rng.s3
                    (count + 1) trace
                else if smallV r p (by omega) (fun h => by have := hcb.2.1 h; omega)
                    (fun h => by have := hcb.2.2 h; omega) then
                  let c' := refreshFromRV W P hP2 D nW numRx rates hB r hcb.1 hcb.2.1
                    hcb.2.2 p (by omega) c hc
                  have hc' : Sized nW P c' := refreshFromRV_sized W P hP2 D nW numRx rates hB r
                    hcb.1 hcb.2.1 hcb.2.2 p (by omega) c hc
                  let trace := if save then trace.push (time, stateOfV p c' n) else trace
                  let total := c'.tree.uget 1 (by
                    have := hc'.2.2
                    rw [one_toNat]
                    omega)
                  if !decide (total < floatInf) then .error (.invalidRate numRx.toNat)
                  else if !decide (floatNegInf < total) then .error (.invalidRate numRx.toNat)
                  else if !decide (floatZero < total) then
                    let st : State := stateOfV p c' n
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
                    let cN := toCacheV C n c
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

/-- Generation 25's start, entering generation 26's driver on networks whose reactions have one,
two or three changes; otherwise generation 21's start, as in generation 25 (whose conditions
are these with two or three changes). -/
def start (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let n := C.gen5.base.ms.size
  let total := c.tree.get! 1
  let W := compileW C codes
  let popW := (toCounts pop).push 0
  let cV : CacheV := ⟨toCounts c.lo, toCounts c.hi, c.tree⟩
  if h : (Gen7.finite total = true ∧ decide (floatZero < total) = true ∧
      2 * C.gen5.base.leaves < USize.size) ∧
      ((pop.size = n ∧ c.lo.size = n ∧ c.hi.size = n ∧ Gen15.validChanges C n = true ∧
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
      W.changes.all (fun chs => chs.size == 1 || chs.size == 2 || chs.size == 3) = true ∧
      C.gen5.base.leaves.toUSize.toNat = 2 ^ C.gen5.base.depth.toUSize.toNat) then
    have hs := h.2
    have hB := boundsOK_spec hs.2.1
    have hnum : C.gen5.base.numRx.toUSize.toNat = C.gen5.base.numRx := by
      rw [Nat.toUSize, USize.toNat_ofNat_of_lt' hs.1.2.2.2.2.2.2.2.2.1]
    run C codes W C.gen5.base.ms n rfl (Gen15.validChanges_spec hs.1.2.2.2.1) n.toUSize
      C.gen5.base.numRx.toUSize C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h.1.2.2)
      C.gen5.base.depth.toUSize C.gen5.base.rates hB (level_root hs.2.2.2.2.2.2.2)
      (buildRxV W C.gen5.base.rates C.gen5.base.numRx)
      (by
        rw [hnum]
        exact buildRxV_ok W C.gen5.base.rates C.gen5.base.numRx
          (by have := hB.changes; omega) hs.2.2.2.2.2.2.1)
      horizon save cap.toUSize fuel.toUSize cap.toUSize popW hs.2.2.1 cV
      ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩
      now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize trace
  else Gen21.start C codes horizon save cap fuel pop c now rng count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(Gen7.finite start && Gen7.finite horizon && decide (start ≤ horizon)) then
    .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen6.compile net
    Gen26.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen26
