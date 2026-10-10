import JumpProcessesLean.Proofs.TreeRSSAGen10
import JumpProcessesLean.TreeRSSA.Gen11

/-!
# Generation 11 is generation 10, hence the specification

The machine-word descent visits the same nodes as `Gen1.descend`: starting from node `1`, a
node of level `i` lies in `[2^i, 2^(i+1))`, so the test `k < P` with `P = 2^depth` fails
exactly after `depth` levels, and every read is in bounds (`descendW_eq`). The driver draws
the exponential and the acceptance uniform before descending; the descent is pure, so this
only moves a `let`. With the descent rewritten, generation 11's driver is generation 10's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

lemma floatArray_uget_eq (a : FloatArray) (i : USize) (h : i.toNat < a.size) :
    a.uget i h = a.get! i.toNat := by
  cases a with
  | mk ds =>
    have h' : i.toNat < ds.size := h
    simp only [FloatArray.uget, FloatArray.get!, getElem!_pos ds i.toNat h']
    rfl

/-- The word descent from a node of level `i` is `Gen1.descend` for the remaining
`depth - i` levels. -/
theorem descendW_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (depth : Nat) (hPd : P.toNat = 2 ^ depth) :
    ∀ n i (k : USize) (hk0 : 0 < k.toNat) (x : Float), i + n = depth → 2 ^ i ≤ k.toNat →
      k.toNat < 2 ^ (i + 1) →
      (Gen11.descendW tree P hP hP2 k hk0 x).toNat = Gen1.descend tree n k.toNat x := by
  intro n
  induction n with
  | zero =>
    intro i k hk0 x hi hlo _
    obtain rfl : i = depth := by omega
    have hkP : ¬ k < P := by
      intro h
      have : k.toNat < P.toNat := h
      omega
    rw [Gen11.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
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
    rw [Gen11.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
    simp only [Gen1.descend, floatArray_uget_eq, h2]
    split
    · rw [← h2]
      exact ih (i + 1) (2 * k) _ x (by omega) (by rw [h2]; omega) (by rw [h2]; omega)
    · rw [show 2 * k.toNat + 1 = (2 * k + 1).toNat from h21.symm]
      exact ih (i + 1) (2 * k + 1) _ _ (by omega) (by rw [h21]; omega) (by rw [h21]; omega)

theorem descendAt_eq (tree : FloatArray) (depth : Nat) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ depth) (x : Float) :
    Gen11.descendAt tree depth P hP2 x = Gen1.descend tree depth 1 x := by
  unfold Gen11.descendAt
  split
  · have h1 : (1 : USize).toNat = 1 := by
      rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
    rw [descendW_eq tree P _ hP2 depth hPd depth 0 1 _ x (by omega) (by rw [h1]; simp)
      (by rw [h1]; simp), h1]
  · rfl

/-- Generation 11's driver from one proposal on is generation 10's, given the statement for
the next event. -/
theorem run11_eq_of (C : Gen6.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float) (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen11.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total elapsed
          s0 s1 s2 s3 count trace =
        Gen10.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total elapsed
          s0 s1 s2 s3 count trace) :
    ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen11.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace =
        Gen10.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen11.run.eq_1, Gen10.run.eq_1]
  | succ pf ih =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen11.run.eq_2, Gen10.run.eq_2]
    simp only [descendAt_eq _ _ _ _ hPd, ih]
    cases fuel with
    | zero => rfl
    | succ f => simp only [hnext f rfl]

theorem gen11_run_eq (C : Gen6.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float) (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen11.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace =
        Gen10.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero => exact run11_eq_of C P hP2 hPd horizon save cap 0 (fun f h => absurd h (by omega))
  | succ f ih =>
    exact run11_eq_of C P hP2 hPd horizon save cap (f + 1) (fun f' h => by cases h; exact ih)

theorem start11_eq (C : Gen6.Compiled) (hC : C.gen5.base.leaves = 2 ^ C.gen5.base.depth)
    (horizon : Float) (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float)
    (rng : Xoshiro) (count : Nat) (trace : Array (Float × State)) :
    Gen11.start C horizon save cap fuel pop c now rng count trace =
      Gen10.start C horizon save cap fuel pop c now rng count trace := by
  unfold Gen11.start Gen10.start
  split
  · rename_i h
    have hPd : C.gen5.base.leaves.toUSize.toNat = 2 ^ C.gen5.base.depth := by
      rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega), hC]
    simp only [gen11_run_eq C _ _ hPd]
  · rfl

lemma gen6_compile_leaves (net : Network Float) :
    (Gen6.compile net).gen5.base.leaves = 2 ^ (Gen6.compile net).gen5.base.depth := rfl

/-- Generation 11 returns what generation 10 returns, on every network and input. -/
theorem gen11_eq_gen10 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen11.simulate net initial start horizon rng maxEvents save cap =
      Gen10.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen11.simulate Gen10.simulate
  simp only [start11_eq _ (gen6_compile_leaves net)]

/-- **Generation 11 is the specification.** For every network whose reactant species are in
range and every input, generation 11 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen11_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen11.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen11_eq_gen10, gen10_simulate_eq net hwf]

end JumpProcessesLean.Proofs
