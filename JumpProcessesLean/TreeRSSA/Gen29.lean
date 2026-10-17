import JumpProcessesLean.TreeRSSA.Gen28

/-!
# Tree-RSSA, generation 29: refresh walks with a fixed start

A refresh re-adds the path of each changed leaf up to the point where it meets the path of the
next changed leaf (`fixUntilR`), testing at every level whether it has met it; the level varies
from walk to walk, so the test's last outcome is often mispredicted. On trees of `2^16` leaves
or more, generation 29's walks first re-add eleven levels without that test (`fixWalkR`): a
write at or above the meeting point lands on an ancestor of the next leaf, which the next leaf's
walk writes again. Smaller trees run generation 26's driver, as generation 28 does.
`Gen29.simulate` is proved equal to `Gen28.simulate` (`Proofs/TreeRSSAGen29.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen29

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)
open Gen18 (ChangeW DepW Compiled compileW staleW bracketLo bracketHi ff2 ofCounts toCounts
  allSmall twoPow25)
open Gen19 (CacheV toCache rateMax)
open Gen20 (Bounds boundsOK boundsOK_spec Sized size_uset one_toNat)
open Gen22 (Level level_lt level_ge level_two_mul_lt level_child two_toNat two_le_toNat
  toNat_sub_two level_root)
open Gen25 (stateOfV toCacheV apply1C)
open Gen26 (RxV buildRxV buildRxV_ok RxOKV evalV applyRV applyRV_size smallV three_le_toNat
  two_le_of_three_le)

/-- `Gen26.descendW`, compiled in this module so that the driver inlines it. -/
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

/-- `Gen26.descend2`, compiled in this module so that the driver inlines it. -/
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

theorem descendW_eq26 (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) :
    descendW tree P hP hP2 k hk0 x = Gen26.descendW tree P hP hP2 k hk0 x := by
  suffices ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      descendW tree P hP hP2 k hk0 x = Gen26.descendW tree P hP hP2 k hk0 x from
    this _ k hk0 x (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
      Gen26.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
  | succ m ih =>
    intro k hk0 x hm
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [descendW, dite_eq_left_of_eq_true (eq_true hkP),
        Gen26.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega)
    · rw [descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
        Gen26.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]

theorem descend2_eq26 (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (d k : USize) (hk : Level P d k) (x : Float) :
    descend2 tree P hP hP2 d k hk x = Gen26.descend2 tree P hP hP2 d k hk x := by
  suffices ∀ m (d k : USize) (hk : Level P d k) (x : Float), d.toNat ≤ m →
      descend2 tree P hP hP2 d k hk x = Gen26.descend2 tree P hP hP2 d k hk x from
    this _ d k hk x (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro d k hk x hm
    have h3 : ¬ 3 ≤ d := fun h => by have := Gen26.three_le_toNat h; omega
    rw [descend2, dite_eq_right h3, Gen26.descend2, dite_eq_right h3]
  | succ m ih =>
    intro d k hk x hm
    by_cases h3 : 3 ≤ d
    · have hd3 : 3 ≤ d.toNat := Gen26.three_le_toNat h3
      have hdd : (d - 2).toNat ≤ m := by
        rw [toNat_sub_two (Gen26.two_le_of_three_le h3)]; omega
      rw [descend2, dite_eq_left h3, Gen26.descend2, dite_eq_left h3]
      simp only [ih (d - 2) _ _ _ hdd]
    · rw [descend2, dite_eq_right h3, Gen26.descend2, dite_eq_right h3]

/-! ## Refreshes -/

/-- `Gen26.fixUntilR`, compiled in this module so that the refreshes inline it. -/
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

/-- `Gen26.fixPathR`, compiled in this module so that the refreshes inline it. -/
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

theorem usizeLit_toNat (c : Nat) (hc : c < 2 ^ 32) : (OfNat.ofNat c : USize).toNat = c := by
  have : c < USize.size := by
    rcases USize.size_eq with h | h <;> rw [h] <;> omega
  exact USize.toNat_ofNat_of_lt' this

/-- `fixUntilR` whose first `w` levels skip the meeting test. A write at or above the meeting
point lands on an ancestor of `other`, which the walk from `other` writes again later. -/
def fixWalkR (P : USize) (n w : USize) (hw : w.toNat ≤ n.toNat) (tree : FloatArray)
    (hP : 2 * P.toNat ≤ tree.size) (node : USize) (hn : node.toNat < 2 * P.toNat) (other : USize)
    (v : Float) : FloatArray :=
  if hz : w = 0 then fixUntilR P n tree hP node hn other v
  else
    have hw0 : w.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp (by rw [h]; rfl))
    have hn0 : n ≠ 0 := fun h => by rw [h] at hw; simp at hw; omega
    let k := node >>> 1
    have hs : (node ^^^ 1).toNat < tree.size := by rw [Gen12.xor_one_toNat]; omega
    have hk : k.toNat < tree.size := by rw [Gen12.shiftRight_one_toNat]; omega
    let v := v + tree.uget (node ^^^ 1) hs
    fixWalkR P (n - 1) (w - 1)
      (by rw [Gen16.pred_toNat n hn0, Gen16.pred_toNat w hz]; omega)
      (tree.uset k v hk) (by rw [Gen12.size_uset]; exact hP) k
      (by rw [Gen12.shiftRight_one_toNat]; omega) (other >>> 1) v
termination_by w.toNat
decreasing_by rw [Gen16.pred_toNat w hz]; omega

theorem fixWalkR_size (P : USize) : ∀ (m : Nat) (n w : USize) (hw : w.toNat ≤ n.toNat),
    w.toNat = m → ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float),
      (fixWalkR P n w hw tree hP node hn other v).size = tree.size := by
  intro m
  induction m with
  | zero =>
    intro n w hw hm tree hP node hn other v
    have hz : w = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [fixWalkR, dite_eq_left hz, fixUntilR_size P _ n rfl]
  | succ m ih =>
    intro n w hw hm tree hP node hn other v
    have hz : w ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [fixWalkR, dite_eq_right hz]
    dsimp only
    rw [ih _ _ _ (by rw [Gen16.pred_toNat w hz]; omega), Gen12.size_uset]

/-- Generation 26's `setBoundsR` with the walks of `fixWalkR`. -/
def setBoundsR (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (hD : 11 ≤ D.toNat) (nW : USize) (hi : FloatArray) (hhi : nW.toNat ≤ hi.size)
    (h0 h1 g0 g1 : Float) (ds : Array DepW)
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
      setBoundsR P hP2 D hD nW hi hhi h0 h1 g0 g1 ds hds (i + 1) tree htree pending hpend
    else if pH == floatZero then
      setBoundsR P hP2 D hD nW hi hhi h0 h1 g0 g1 ds hds (i + 1) tree htree pending hpend
    else
      let leaf := P + d.k
      have hleaf : leaf.toNat = P.toNat + d.k.toNat := by
        have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hpend' : pending ≠ 0 → pending.toNat < 2 * P.toNat := fun hz => hpend.resolve_left hz
      let tree' := if hz : pending = 0 then tree
        else fixWalkR P D 11 (by rw [usizeLit_toNat 11 (by omega)]; exact hD) tree htree
          pending (hpend' hz) leaf (tree.uget pending (by have := hpend' hz; omega))
      have htree' : 2 * P.toNat ≤ tree'.size := by
        simp only [tree']
        split
        · exact htree
        · rw [fixWalkR_size P _ D _ _ rfl]; exact htree
      setBoundsR P hP2 D hD nW hi hhi h0 h1 g0 g1 ds hds (i + 1)
        (tree'.uset leaf (d.rate * (bN * pH)) (by omega)) (by rw [size_uset]; exact htree') leaf
        (Or.inr (by omega))
  else if hz : pending = 0 then tree
    else fixPathR P D tree htree pending (hpend.resolve_left hz)
      (tree.uget pending (by have := hpend.resolve_left hz; omega))
termination_by ds.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize ds i h]; omega)

theorem setBoundsR_size (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (hD : 11 ≤ D.toNat) (nW : USize) (hi : FloatArray) (hhi : nW.toNat ≤ hi.size)
    (h0 h1 g0 g1 : Float) (ds : Array DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat) :
    ∀ m (i : USize), ds.size - i.toNat = m → ∀ (tree : FloatArray)
      (htree : 2 * P.toNat ≤ tree.size) (pending : USize) hpend,
      (setBoundsR P hP2 D hD nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend).size =
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
        | (rw [ih (i + 1) (by omega), size_uset, fixWalkR_size P _ D _ _ rfl])
        | (rw [ih (i + 1) (by omega), size_uset])
    · rw [setBoundsR, dite_eq_right h]
      split
      · rfl
      · rw [fixPathR_size P _ D rfl]

/-- `Gen26.rebracketR` through this module's `setBoundsR`. -/
@[inline] def rebracketR (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (hD : 11 ≤ D.toNat) (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (c : CacheV) (hc : Sized nW P c) (s : USize)
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
  ⟨lo, hi, setBoundsR P hP2 D hD nW hi (by rw [size_uset]; exact Nat.le_of_eq hc.2.1.symm) hiN
    (ff2 hiN) hiS (ff2 hiS)
    (W.deps.uget s (by omega)) (fun k h => hB.depKP s.toNat (by omega) k h) 0 c.tree
    (Nat.le_of_eq hc.2.2.symm) 0 (Or.inl rfl)⟩

theorem rebracketR_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (hD : 11 ≤ D.toNat) (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (c : CacheV) (hc : Sized nW P c) (s : USize)
    (hs : s.toNat < nW.toNat) :
    Sized nW P (rebracketR W P hP2 D hD nW numRx rates hB pop hpop c hc s hs) := by
  refine ⟨?_, ?_, ?_⟩
  · show (c.lo.uset _ _ _).size = nW.toNat
    rw [size_uset]; exact hc.1
  · show (c.hi.uset _ _ _).size = nW.toNat
    rw [size_uset]; exact hc.2.1
  · show (setBoundsR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).size = 2 * P.toNat
    rw [setBoundsR_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 rfl]
    exact hc.2.2


/-- `Gen26.refresh1` through this module's `rebracketR`. -/
@[inline] def refresh1 (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (hD : 11 ≤ D.toNat) (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (s : USize) (hs : s.toNat < nW.toNat)
    (c : CacheV) (hc : Sized nW P c) : CacheV :=
  have hms := hB.ms
  if staleW (W.ms.uget s (by omega)) (pop.uget s (by omega))
      (c.lo.uget s (by have := hc.1; omega)) (c.hi.uget s (by have := hc.2.1; omega)) then
    rebracketR W P hP2 D hD nW numRx rates hB pop hpop c hc s hs
  else c

theorem refresh1_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (hD : 11 ≤ D.toNat) (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (s : USize) (hs : s.toNat < nW.toNat)
    (c : CacheV) (hc : Sized nW P c) :
    Sized nW P (refresh1 W P hP2 D hD nW numRx rates hB pop hpop s hs c hc) := by
  simp only [refresh1]
  split
  · exact rebracketR_sized W P hP2 D hD nW numRx rates hB pop hpop c hc s hs
  · exact hc

/-- `Gen26.refreshFromRV` through this module's `refresh1`. -/
def refreshFromRV (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (hD : 11 ≤ D.toNat) (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates)
    (r : RxV) (h0 : r.c0.toNat < nW.toNat) (h1 : r.one = false → r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (c : CacheV) (hc : Sized nW P c) : CacheV :=
  let c0 := refresh1 W P hP2 D hD nW numRx rates hB pop hpop r.c0 h0 c hc
  have e0 := refresh1_sized W P hP2 D hD nW numRx rates hB pop hpop r.c0 h0 c hc
  if h1' : r.one = true then c0
  else
    have h1'' : r.c1.toNat < nW.toNat := h1 (by simpa using h1')
    let c1 := refresh1 W P hP2 D hD nW numRx rates hB pop hpop r.c1 h1'' c0 e0
    have e1 := refresh1_sized W P hP2 D hD nW numRx rates hB pop hpop r.c1 h1'' c0 e0
    if h : r.three = true then refresh1 W P hP2 D hD nW numRx rates hB pop hpop r.c2 (h2 h) c1 e1
    else c1

theorem refreshFromRV_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (hD : 11 ≤ D.toNat) (nW numRx : USize) (rates : FloatArray)
    (hB : Bounds W nW P numRx rates) (r : RxV) (h0 : r.c0.toNat < nW.toNat)
    (h1 : r.one = false → r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (c : CacheV) (hc : Sized nW P c) :
    Sized nW P (refreshFromRV W P hP2 D hD nW numRx rates hB r h0 h1 h2 pop hpop c hc) := by
  simp only [refreshFromRV]
  split
  · exact refresh1_sized _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · split
    · exact refresh1_sized _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · exact refresh1_sized _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## The driver -/

/-- Generation 26's driver through this module's refreshes, on trees of depth at least 11. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Compiled) (msN : Array Nat) (n : Nat)
    (hms : msN.size = n) (hval : Gen15.ValidChanges C n) (nW : USize) (numRx : USize) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (hD : 11 ≤ D.toNat)
    (rates : FloatArray)
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
              have hw := Gen26.descendW_lt c.tree P htree hP2 _ 1 Gen11.usize_one_pos (u * total)
                (Nat.le_refl _) (by rw [one_toNat]; omega)
              simp only [k]
              split
              · rw [descend2_eq26, Gen26.descend2_eq c.tree P htree hP2 _ D 1 hL
                  Gen11.usize_one_pos (u * total) (Nat.le_refl _)]
                exact hw
              · rw [descendW_eq26]; exact hw
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
                  run C codes W msN n hms hval nW numRx P hP2 D hD rates hB hL rxs hR horizon save cap
                    (evFuel - 1) cap p hp c hc time total floatZero rng.s0 rng.s1 rng.s2 rng.s3
                    (count + 1) trace
                else if smallV r p (by omega) (fun h => by have := hcb.2.1 h; omega)
                    (fun h => by have := hcb.2.2 h; omega) then
                  let c' := refreshFromRV W P hP2 D hD nW numRx rates hB r hcb.1 hcb.2.1
                    hcb.2.2 p (by omega) c hc
                  have hc' : Sized nW P c' := refreshFromRV_sized W P hP2 D hD nW numRx rates hB r
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
                    run C codes W msN n hms hval nW numRx P hP2 D hD rates hB hL rxs hR horizon save
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
              run C codes W msN n hms hval nW numRx P hP2 D hD rates hB hL rxs hR horizon save cap
                evFuel (prFuel - 1) pop hpop c hc now total elapsed rng.s0 rng.s1 rng.s2 rng.s3
                count trace
termination_by (evFuel.toNat, prFuel.toNat)
decreasing_by
  all_goals first
    | (have : evFuel.toNat ≠ 0 := fun h => he (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat evFuel he]; exact Prod.Lex.left _ _ (by omega))
    | (have : prFuel.toNat ≠ 0 := fun h => _hz (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat prFuel _hz]; exact Prod.Lex.right _ (by omega))

/-- Generation 28's start, entering this module's driver on trees of depth at least 16. -/
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
      Gen28.changesOK C = true ∧ Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
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
    if hD : 16 ≤ C.gen5.base.depth.toUSize.toNat then
      run C codes W C.gen5.base.ms n rfl (Gen15.validChanges_spec hs.1.2.2.2.1) n.toUSize
        C.gen5.base.numRx.toUSize C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h.1.2.2)
        C.gen5.base.depth.toUSize (by omega) C.gen5.base.rates hB (level_root hs.2.2.2.2.2.2.2)
        (buildRxV W C.gen5.base.rates C.gen5.base.numRx)
        (by
          rw [hnum]
          exact buildRxV_ok W C.gen5.base.rates C.gen5.base.numRx
            (by have := hB.changes; omega) hs.2.2.2.2.2.2.1)
        horizon save cap.toUSize fuel.toUSize cap.toUSize popW hs.2.2.1 cV
        ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩
        now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize trace
    else
      Gen26.run C codes W C.gen5.base.ms n rfl (Gen15.validChanges_spec hs.1.2.2.2.1) n.toUSize
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
  else Gen21.start C codes horizon save cap fuel pop
    { c with lower := ⟨C.gen5.base.net.reactions.map (Gen2.rate · c.lo)⟩ } now rng count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(Gen7.finite start && Gen7.finite horizon && decide (start ≤ horizon)) then
    .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen27.compile net
    Gen29.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      ⟨initial.lo, initial.hi, ⟨#[]⟩, Gen27.initialTree C.gen5.base initial.hi⟩ start rng 0
      #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen29
