import JumpProcessesLean.Proofs.TreeRSSAGen11
import JumpProcessesLean.TreeRSSA.Gen12

/-!
# Generation 12 is generation 11, hence the specification

Float addition is commutative in Lean's model of `Float`: not-a-number carries no payload,
and two finite values are added as integers at the smaller exponent (`float_add_comm`). So
the sum of a node's children is the carried value plus the sibling, whichever child the
carried node is (`sibling_sum`). Walking up from a node whose value is carried, `fixUntilGo`
and `fixPathGo` write exactly the sums `Gen3.fixUntil` and `Gen1.fixPath` write, since each
level reads back the value just written (`fixUntilGo_eq`, `fixPathGo_eq`). With the paths and
the module's copy of the descent rewritten, generation 12's refresh, firing and driver are
generation 11's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

theorem unpacked_add_comm (spec : Float.Model.Format) (x y : Float.Model.UnpackedFloat) :
    Float.Model.UnpackedFloat.add spec x y = Float.Model.UnpackedFloat.add spec y x := by
  cases x with
  | notANumber => cases y <;> rfl
  | infinity s₁ =>
    cases y with
    | notANumber => rfl
    | infinity s₂ => cases s₁ <;> cases s₂ <;> rfl
    | zero _ => rfl
    | finite _ _ _ _ => rfl
  | zero s₁ =>
    cases y with
    | notANumber => rfl
    | infinity _ => rfl
    | zero s₂ => cases s₁ <;> cases s₂ <;> rfl
    | finite _ _ _ _ => rfl
  | finite s₁ m₁ e₁ h₁ =>
    cases y with
    | notANumber => rfl
    | infinity _ => rfl
    | zero _ => rfl
    | finite s₂ m₂ e₂ h₂ =>
      simp only [Float.Model.UnpackedFloat.add, Int.min_comm e₁ e₂, Int.add_comm]

/-- **Float addition is commutative** in Lean's model of `Float`. -/
theorem float_add_comm (a b : Float) : a + b = b + a := by
  show Float.add a b = Float.add b a
  unfold Float.add
  congr 1
  show Float.Model.add a.toModel b.toModel = Float.Model.add b.toModel a.toModel
  unfold Float.Model.add
  rw [unpacked_add_comm]

lemma floatArray_uset_eq (a : FloatArray) (i : USize) (v : Float) (h : i.toNat < a.size) :
    a.uset i v h = a.set! i.toNat v := by
  cases a with
  | mk ds =>
    have h' : i.toNat < ds.size := h
    simp only [FloatArray.uset, FloatArray.set!, Array.uset, Array.set!_eq_setIfInBounds,
      Array.setIfInBounds_def, h', ↓reduceDIte]

lemma floatArray_get!_set!_self (a : FloatArray) (i : Nat) (v : Float) (h : i < a.size) :
    (a.set! i v).get! i = v := by
  cases a with
  | mk ds =>
    have h' : i < ds.size := h
    simp [FloatArray.set!, FloatArray.get!, h']

lemma sibling_sum (tree : FloatArray) (node : USize) (v : Float)
    (hv : tree.get! node.toNat = v) :
    v + tree.get! (node ^^^ 1).toNat =
      tree.get! (2 * (node.toNat / 2)) + tree.get! (2 * (node.toNat / 2) + 1) := by
  rw [Gen12.xor_one_toNat]
  rcases Nat.mod_two_eq_zero_or_one node.toNat with h | h
  · rw [h, show 2 * (node.toNat / 2) = node.toNat by omega, hv]
  · rw [h, show 2 * (node.toNat / 2) + 1 = node.toNat by omega, hv, float_add_comm]
    simp

theorem fixUntilGo_eq (P : USize) : ∀ n tree hP node hn other v,
    tree.get! node.toNat = v →
    Gen12.fixUntilGo P n tree hP node hn other v = Gen3.fixUntil tree n node.toNat other.toNat := by
  intro n
  induction n with
  | zero => intro tree hP node hn other v _; rfl
  | succ n ih =>
    intro tree hP node hn other v hv
    rw [Gen12.fixUntilGo, Gen3.fixUntil]
    have hk : (node >>> 1).toNat = node.toNat / 2 := Gen12.shiftRight_one_toNat node
    have ho : (other >>> 1).toNat = other.toNat / 2 := Gen12.shiftRight_one_toNat other
    by_cases hko : node.toNat / 2 = other.toNat / 2
    · have : node >>> 1 = other >>> 1 := USize.toNat_inj.mp (by rw [hk, ho, hko])
      rw [ite_eq_left this]
      simp only [hko, ↓reduceIte]
    · have : ¬ node >>> 1 = other >>> 1 := fun h => hko (by rw [← hk, ← ho, h])
      rw [ite_eq_right this, ite_eq_right hko]
      simp only []
      rw [ih]
      · rw [floatArray_uset_eq, floatArray_uget_eq, sibling_sum tree node v hv, hk, ho]
      · rw [floatArray_uset_eq, hk]
        apply floatArray_get!_set!_self
        omega

theorem fixPathGo_eq (P : USize) : ∀ n tree hP node hn v,
    tree.get! node.toNat = v →
    Gen12.fixPathGo P n tree hP node hn v = Gen1.fixPath tree n node.toNat := by
  intro n
  induction n with
  | zero => intro tree hP node hn v _; rfl
  | succ n ih =>
    intro tree hP node hn v hv
    rw [Gen12.fixPathGo, Gen1.fixPath]
    have hk : (node >>> 1).toNat = node.toNat / 2 := Gen12.shiftRight_one_toNat node
    rw [ih]
    · rw [floatArray_uset_eq, floatArray_uget_eq, sibling_sum tree node v hv, hk]
    · rw [floatArray_uset_eq, hk]
      apply floatArray_get!_set!_self
      omega

theorem fixUntilAt_eq (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray)
    (depth node other : Nat) :
    Gen12.fixUntilAt P hP2 tree depth node other = Gen3.fixUntil tree depth node other := by
  unfold Gen12.fixUntilAt
  split
  · rename_i h
    rw [fixUntilGo_eq _ _ _ _ _ _ _ _ (floatArray_uget_eq _ _ _).symm,
      Gen12.toUSize_toNat_of_lt h.2.1 hP2, Gen12.toUSize_toNat_of_lt h.2.2 hP2]
  · rfl

theorem fixPathAt_eq (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray)
    (depth node : Nat) :
    Gen12.fixPathAt P hP2 tree depth node = Gen1.fixPath tree depth node := by
  unfold Gen12.fixPathAt
  split
  · rename_i h
    rw [fixPathGo_eq _ _ _ _ _ _ _ (floatArray_uget_eq _ _ _).symm,
      Gen12.toUSize_toNat_of_lt h.2 hP2]
  · rfl

theorem setBounds12_eq (C : Gen3.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (lo hi : Array Nat) (s loS hiS : Nat) (ks : Array Nat) (fs : Array Gen3.Factor)
    (rs : FloatArray) : ∀ i lower tree pending,
    Gen12.setBounds C P hP2 lo hi s loS hiS ks fs rs i lower tree pending =
      Gen5.setBounds C lo hi s loS hiS ks fs rs i lower tree pending := by
  intro i
  induction i with
  | zero => intro lower tree pending; simp only [Gen12.setBounds, Gen5.setBounds, fixPathAt_eq]
  | succ i ih =>
    intro lower tree pending
    simp only [Gen12.setBounds, Gen5.setBounds, fixUntilAt_eq, ih]

theorem rebracket12_eq (C : Gen5.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (pop : Array Nat) (c : Cache) (s : Nat) :
    Gen12.rebracket C P hP2 pop c s = Gen7.rebracket C pop c s := by
  simp only [Gen12.rebracket, Gen7.rebracket, setBounds12_eq]

theorem fire12_eq (C : Gen6.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (ms pop : Array Nat) (c : Cache) (j : Nat) :
    Gen12.fire C P hP2 ms pop c j = Gen9.fire C ms pop c j := by
  simp only [Gen12.fire, Gen9.fire, Gen12.refresh, Gen9.refresh, rebracket12_eq]


theorem descendW12_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (depth : Nat) (hPd : P.toNat = 2 ^ depth) :
    ∀ n i (k : USize) (hk0 : 0 < k.toNat) (x : Float), i + n = depth → 2 ^ i ≤ k.toNat →
      k.toNat < 2 ^ (i + 1) →
      (Gen12.descendW tree P hP hP2 k hk0 x).toNat = Gen1.descend tree n k.toNat x := by
  intro n
  induction n with
  | zero =>
    intro i k hk0 x hi hlo _
    obtain rfl : i = depth := by omega
    have hkP : ¬ k < P := by
      intro h
      have : k.toNat < P.toNat := h
      omega
    rw [Gen12.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
    rfl
  | succ n ih =>
    intro i k hk0 x hi hlo hhi
    have hpow : 2 ^ (i + 1) ≤ 2 ^ depth := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hkP' : k.toNat < P.toNat := by omega
    have hkP : k < P := hkP'
    have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
    have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
    have hs1 : 2 ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
    have hs0 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ]; omega
    rw [Gen12.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
    simp only [Gen1.descend, floatArray_uget_eq, h2]
    split
    · rw [← h2]
      exact ih (i + 1) (2 * k) _ x (by omega) (by rw [h2]; omega) (by rw [h2]; omega)
    · rw [show 2 * k.toNat + 1 = (2 * k + 1).toNat from h21.symm]
      exact ih (i + 1) (2 * k + 1) _ _ (by omega) (by rw [h21]; omega) (by rw [h21]; omega)

theorem descendAt12_eq (tree : FloatArray) (depth : Nat) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ depth) (x : Float) :
    Gen12.descendAt tree depth P hP2 x = Gen1.descend tree depth 1 x := by
  unfold Gen12.descendAt
  split
  · have h1 : (1 : USize).toNat = 1 := by
      rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
    rw [descendW12_eq tree P _ hP2 depth hPd depth 0 1 _ x (by omega) (by rw [h1]; simp)
      (by rw [h1]; simp), h1]
  · rfl

/-- Generation 12's driver from one proposal on is generation 11's, given the statement for
the next event. -/
theorem run12_eq_of (C : Gen6.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float) (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen12.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total elapsed
          s0 s1 s2 s3 count trace =
        Gen11.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total elapsed
          s0 s1 s2 s3 count trace) :
    ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen12.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace =
        Gen11.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen12.run.eq_1, Gen11.run.eq_1]
  | succ pf ih =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen12.run.eq_2, Gen11.run.eq_2]
    simp only [descendAt12_eq _ _ _ _ hPd, descendAt_eq _ _ _ _ hPd, fire12_eq, ih]
    cases fuel with
    | zero => rfl
    | succ f => simp only [hnext f rfl]

theorem gen12_run_eq (C : Gen6.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float) (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen12.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace =
        Gen11.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero => exact run12_eq_of C P hP2 hPd horizon save cap 0 (fun f h => absurd h (by omega))
  | succ f ih =>
    exact run12_eq_of C P hP2 hPd horizon save cap (f + 1) (fun f' h => by cases h; exact ih)

theorem start12_eq (C : Gen6.Compiled) (hC : C.gen5.base.leaves = 2 ^ C.gen5.base.depth)
    (horizon : Float) (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float)
    (rng : Xoshiro) (count : Nat) (trace : Array (Float × State)) :
    Gen12.start C horizon save cap fuel pop c now rng count trace =
      Gen11.start C horizon save cap fuel pop c now rng count trace := by
  unfold Gen12.start Gen11.start
  split
  · rename_i h
    have hPd : C.gen5.base.leaves.toUSize.toNat = 2 ^ C.gen5.base.depth := by
      rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega), hC]
    simp only [gen12_run_eq C _ _ hPd]
  · rfl

/-- Generation 12 returns what generation 11 returns, on every network and input. -/
theorem gen12_eq_gen11 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen12.simulate net initial start horizon rng maxEvents save cap =
      Gen11.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen12.simulate Gen11.simulate
  simp only [start12_eq _ (gen6_compile_leaves net)]

/-- **Generation 12 is the specification.** For every network whose reactant species are in
range and every input, generation 12 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen12_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen12.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen12_eq_gen11, gen11_simulate_eq net hwf]

end JumpProcessesLean.Proofs
