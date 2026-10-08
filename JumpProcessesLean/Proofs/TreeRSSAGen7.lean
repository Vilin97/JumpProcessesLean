import JumpProcessesLean.Proofs.TreeRSSAGen6
import JumpProcessesLean.TreeRSSA.Gen7

/-!
# Generation 7 is generation 6, hence the specification

In Lean's model of `Float`, finiteness and the order are both decided by a case analysis on
the unpacked value: not-a-number, an infinity, a zero or a finite value. A float is finite
exactly when it is below `+∞` and above `-∞`. With that, generation 7's driver is generation
6's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

theorem inf_unpack : Float.Model.inf.unpack = .infinity .positive := by rfl

theorem negInf_unpack : (-Float.Model.inf).unpack = .infinity .negative := by rfl

theorem decide_float_lt (a b : Float) :
    decide (a < b) = a.toModel.unpack.lt b.toModel.unpack := by
  show decide (Float.lt a b = true) = _
  rw [Bool.decide_eq_true]
  unfold Float.lt
  show decide (a.toModel.lt b.toModel = true) = _
  rw [Bool.decide_eq_true]
  rfl

/-- **A float is finite exactly when it lies strictly between the two infinities.** -/
theorem isFinite_eq_lt (x : Float) :
    x.isFinite = (decide (x < Gen7.floatInf) && decide (Gen7.floatNegInf < x)) := by
  rw [decide_float_lt, decide_float_lt]
  show x.toModel.unpack.isFinite = (x.toModel.unpack.lt Float.Model.inf.unpack &&
    (-Float.Model.inf).unpack.lt x.toModel.unpack)
  rw [inf_unpack, negInf_unpack]
  generalize x.toModel.unpack = u
  cases u with
  | notANumber => rfl
  | infinity s => cases s <;> rfl
  | zero s => cases s <;> rfl
  | finite s m e h => cases s <;> rfl

lemma finite_eq (x : Float) : Gen7.finite x = x.isFinite := (isFinite_eq_lt x).symm

lemma gen7_refresh_eq (C : Gen5.Compiled) (pop : Array Nat) (c : Cache) (s : Nat) :
    Gen7.refresh C pop c s = Gen5.refresh C pop c s := rfl

lemma gen7_fire_eq (C : Gen6.Compiled) (pop : Array Nat) (c : Cache) (j : Nat) :
    Gen7.fire C pop c j = Gen6.fire C pop c j := rfl

/-- Generation 7's driver from one proposal on is generation 6's, given the statement for the
next event. -/
theorem run7_eq_of (C : Gen6.Compiled) (horizon : Float) (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen7.run C horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen6.run C horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen7.run C horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen6.run C horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count
          trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen7.run.eq_1, Gen6.run.eq_1]
  | succ pf ih =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen7.run.eq_2, Gen6.run.eq_2]
    simp only [finite_eq]
    rcases h1 : Xoshiro.uniform ⟨s0, s1, s2, s3⟩ with ⟨u, r1⟩
    dsimp only
    by_cases hu : (!(u.isFinite && decide (floatZero ≤ u) && decide (u < floatOne))) = true
    · simp only [hu, ↓reduceIte]
    simp only [hu, Bool.false_eq_true, ↓reduceIte]
    rcases h2 : r1.exponential with ⟨e, r2⟩
    dsimp only
    by_cases he : (!(e.isFinite && decide (floatZero < e))) = true
    · simp only [he, ↓reduceIte]
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    by_cases hel : (!(elapsed + e).isFinite) = true
    · simp only [hel, ↓reduceIte]
    simp only [hel, Bool.false_eq_true, ↓reduceIte]
    rcases h3 : r2.uniform with ⟨v, r3⟩
    dsimp only
    by_cases hv : (!(v.isFinite && decide (floatZero ≤ v) && decide (v < floatOne))) = true
    · simp only [hv, ↓reduceIte]
    simp only [hv, Bool.false_eq_true, ↓reduceIte]
    generalize Gen1.descend c.tree C.gen5.base.depth 1 (u * total) - C.gen5.base.leaves = j
    by_cases hacc : (decide (j < C.gen5.base.numRx) &&
        ((decide (floatZero < c.lower.get! j) &&
            decide (v * c.tree.get! (C.gen5.base.leaves + j) ≤ c.lower.get! j)) ||
          (decide (floatZero < Gen3.rate C.gen5.base j pop) &&
            decide (v * c.tree.get! (C.gen5.base.leaves + j) ≤ Gen3.rate C.gen5.base j pop)))) =
        true
    · simp only [hacc, ↓reduceIte]
      generalize now + (elapsed + e) / total = time
      by_cases ht : (!(time.isFinite && decide (now < time))) = true
      · simp only [ht, ↓reduceIte]
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      by_cases hle : (!decide (now ≤ time)) = true
      · simp only [hle, ↓reduceIte]
      simp only [hle, Bool.false_eq_true, ↓reduceIte]
      by_cases hh : (!decide (time ≤ horizon)) = true
      · simp only [hh, ↓reduceIte]
      simp only [hh, Bool.false_eq_true, ↓reduceIte]
      cases fuel with
      | zero => rfl
      | succ f =>
        dsimp only
        rw [gen7_fire_eq]
        rcases Gen6.fire C pop c j with ⟨pop', c'⟩
        dsimp only
        by_cases hfin' : (!(c'.tree.get! 1).isFinite) = true
        · simp only [hfin', ↓reduceIte]
        simp only [hfin', Bool.false_eq_true, ↓reduceIte]
        by_cases hpos : (!decide (floatZero < c'.tree.get! 1)) = true
        · simp only [hpos, ↓reduceIte]
        simp only [hpos, Bool.false_eq_true, ↓reduceIte]
        rw [hnext f rfl]
    · simp only [hacc, Bool.false_eq_true, ↓reduceIte]
      rw [ih]

theorem gen7_run_eq (C : Gen6.Compiled) (horizon : Float) (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen7.run C horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen6.run C horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count
          trace := by
  intro fuel
  induction fuel with
  | zero => exact run7_eq_of C horizon save cap 0 (fun f h => absurd h (by omega))
  | succ f ih => exact run7_eq_of C horizon save cap (f + 1) (fun f' h => by cases h; exact ih)

/-- Generation 7 returns what generation 6 returns, on every network and input. -/
theorem gen7_eq_gen6 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen7.simulate net initial start horizon rng maxEvents save cap =
      Gen6.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen7.simulate Gen6.simulate Gen7.start Gen6.start
  simp only [finite_eq, gen7_run_eq]

/-- **Generation 7 is the specification.** For every network whose reactant species are in
range and every input, generation 7 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen7_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen7.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen7_eq_gen6, gen6_simulate_eq net hwf]

end JumpProcessesLean.Proofs
