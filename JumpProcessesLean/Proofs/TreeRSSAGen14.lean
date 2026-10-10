import JumpProcessesLean.Proofs.TreeRSSAGen13
import JumpProcessesLean.TreeRSSA.Gen14

/-!
# Generation 14 is generation 13, hence the specification

When the tree has `2P` slots, generation 13's descent is its word descent, and both modules'
word descents are `Gen1.descend` (`descendW14_eq`); otherwise generation 14's proposal is
generation 13's by definition. So generation 14's driver is generation 13's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

theorem descendW14_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (depth : Nat) (hPd : P.toNat = 2 ^ depth) :
    ∀ n i (k : USize) (hk0 : 0 < k.toNat) (x : Float), i + n = depth → 2 ^ i ≤ k.toNat →
      k.toNat < 2 ^ (i + 1) →
      (Gen14.descendW tree P hP hP2 k hk0 x).toNat = Gen1.descend tree n k.toNat x := by
  intro n
  induction n with
  | zero =>
    intro i k hk0 x hi hlo _
    obtain rfl : i = depth := by omega
    have hkP : ¬ k < P := by
      intro h
      have : k.toNat < P.toNat := h
      omega
    rw [Gen14.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
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
    rw [Gen14.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
    simp only [Gen1.descend, floatArray_uget_eq, h2]
    split
    · rw [← h2]
      exact ih (i + 1) (2 * k) _ x (by omega) (by rw [h2]; omega) (by rw [h2]; omega)
    · rw [show 2 * k.toNat + 1 = (2 * k + 1).toNat from h21.symm]
      exact ih (i + 1) (2 * k + 1) _ _ (by omega) (by rw [h21]; omega) (by rw [h21]; omega)

/-- Generation 14's driver from one proposal on is generation 13's, given the statement for
the next event. -/
theorem run14_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float)
    (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen14.run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P
          hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace =
        Gen13.run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P
          hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen14.run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P
          hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace =
        Gen13.run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P
          hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen14.run.eq_1, Gen13.run.eq_1]
  | succ pf ih =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen14.run.eq_2]
    by_cases hT : 2 * P ≤ c.tree.usize
    · rw [dite_eq_left_of_eq_true (eq_true hT), Gen13.run.eq_2]
      have h1 : (1 : USize).toNat = 1 := by
        rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
      have hd : ∀ x, (Gen14.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
          Gen11.usize_one_pos x).toNat = Gen1.descend c.tree C.gen5.base.depth 1 x := by
        intro x
        rw [descendW14_eq c.tree P _ hP2 C.gen5.base.depth hPd C.gen5.base.depth 0 1 _ x
          (by omega) (by rw [h1]; simp) (by rw [h1]; simp), h1]
      simp only [hd, descendAt13_eq _ _ _ _ hPd, ih]
      cases fuel with
      | zero => rfl
      | succ f => simp only [hnext f rfl]
    · rw [dite_eq_right_iff.mpr (fun h => absurd h hT)]

theorem gen14_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float)
    (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen14.run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P
          hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace =
        Gen13.run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P
          hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run14_eq_of C codes P hP2 hPd horizon save cap 0 (fun f h => absurd h (by omega))
  | succ f ih =>
    exact run14_eq_of C codes P hP2 hPd horizon save cap (f + 1)
      (fun f' h => by cases h; exact ih)

theorem start14_eq (C : Gen6.Compiled) (codes : Array (Array Nat))
    (hC : C.gen5.base.leaves = 2 ^ C.gen5.base.depth) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) :
    Gen14.start C codes horizon save cap fuel pop c now rng count trace =
      Gen13.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen14.start Gen13.start
  split
  · rename_i h
    have hPd : C.gen5.base.leaves.toUSize.toNat = 2 ^ C.gen5.base.depth := by
      rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega), hC]
    simp only [gen14_run_eq C codes _ _ hPd]
  · rfl

/-- Generation 14 returns what generation 13 returns, on every network and input. -/
theorem gen14_eq_gen13 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen14.simulate net initial start horizon rng maxEvents save cap =
      Gen13.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen14.simulate Gen13.simulate
  simp only [start14_eq _ _ (gen6_compile_leaves net)]

/-- **Generation 14 is the specification.** For every network whose reactant species are in
range and every input, generation 14 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen14_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen14.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen14_eq_gen13, gen13_simulate_eq net hwf]

end JumpProcessesLean.Proofs
