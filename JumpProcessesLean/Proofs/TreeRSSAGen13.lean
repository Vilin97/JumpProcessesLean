import JumpProcessesLean.Proofs.TreeRSSAGen12
import JumpProcessesLean.TreeRSSA.Gen13

/-!
# Generation 13 is generation 12, hence the specification

A dependent of species `s` whose compiled factor is `ff(x_s, ν)` alone, or `ff(x_s, ν)` times
`ff(x_t, μ)` for another species `t` (in either order), gets a code from which `own` recovers
`ff(·, ν)` and `partner` recovers `ff(x_t, μ)`. Its factor at a bracket array is the power of
`s`'s entry times the partner factor, and with `s` read at its old value it is the power of the
old value times the same partner factor (`code_eval`). Every other factor gets the code `2` and
is evaluated as in generation 12. So generation 13's refresh computes generation 12's natural
numbers, and its driver is generation 12's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

lemma ffb_ff (x ν : Nat) (h : ν = 1 ∨ ν = 2) : Gen13.ffb x (ν - 1) = Gen3.ff x ν := by
  rcases h with rfl | rfl <;> simp [Gen13.ffb, Gen3.ff]

lemma code_decode (u a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    (4 * (u + 1) + 2 * a + b) % 2 = b ∧ ¬ (4 * (u + 1) + 2 * a + b < 4) ∧
      (4 * (u + 1) + 2 * a + b) / 4 - 1 = u ∧ (4 * (u + 1) + 2 * a + b) / 2 % 2 = a := by
  omega

lemma pair_own_partner (u ν μ x : Nat) (arr : Array Nat) (hν : ν = 1 ∨ ν = 2)
    (hμ : μ = 1 ∨ μ = 2) :
    Gen13.own (4 * (u + 1) + 2 * (μ - 1) + (ν - 1)) x = Gen3.ff x ν ∧
      Gen13.partner (4 * (u + 1) + 2 * (μ - 1) + (ν - 1)) arr = Gen3.ff arr[u]! μ := by
  obtain ⟨h1, h2, h3, h4⟩ := code_decode u (μ - 1) (ν - 1) (by omega) (by omega)
  simp only [Gen13.own, Gen13.partner, h1, h2, h3, h4, ↓reduceIte]
  exact ⟨ffb_ff x ν hν, ffb_ff _ μ hμ⟩

/-- The integer factor of a dependent with a non-fallback code is the power of the refreshed
species times the partner factor, both in the factor's evaluation and with the refreshed
species read at another value. -/
theorem code_eval (s : Nat) (f : Gen3.Factor) (hc : Gen13.code s f ≠ 2) :
    (∀ arr : Array Nat, f.eval arr = Gen13.own (Gen13.code s f) arr[s]! *
      Gen13.partner (Gen13.code s f) arr) ∧
    (∀ (arr : Array Nat) (v : Nat), Gen5.evalAt f arr s v = Gen13.own (Gen13.code s f) v *
      Gen13.partner (Gen13.code s f) arr) := by
  cases f with
  | one t =>
    by_cases ht : t = s
    · subst ht
      simp [Gen13.code, Gen13.own, Gen13.partner, Gen13.ffb, Gen3.Factor.eval, Gen5.evalAt]
    · simp [Gen13.code, ht] at hc
  | two t =>
    by_cases ht : t = s
    · subst ht
      simp [Gen13.code, Gen13.own, Gen13.partner, Gen13.ffb, Gen3.Factor.eval, Gen5.evalAt]
    · simp [Gen13.code, ht] at hc
  | pair t ν u μ =>
    by_cases hA : t = s ∧ u ≠ s ∧ (ν = 1 ∨ ν = 2) ∧ (μ = 1 ∨ μ = 2)
    · have hcode : Gen13.code s (.pair t ν u μ) = 4 * (u + 1) + 2 * (μ - 1) + (ν - 1) := by
        simp only [Gen13.code]; exact ite_eq_left hA
      obtain ⟨rfl, hu, hν, hμ⟩ := hA
      rw [hcode]
      refine ⟨fun arr => ?_, fun arr v => ?_⟩
      · rw [(pair_own_partner u ν μ arr[t]! arr hν hμ).1, (pair_own_partner u ν μ 0 arr hν hμ).2]
        rfl
      · rw [(pair_own_partner u ν μ v arr hν hμ).1, (pair_own_partner u ν μ 0 arr hν hμ).2]
        simp [Gen5.evalAt, hu]
    · by_cases hB : u = s ∧ t ≠ s ∧ (ν = 1 ∨ ν = 2) ∧ (μ = 1 ∨ μ = 2)
      · have hcode : Gen13.code s (.pair t ν u μ) = 4 * (t + 1) + 2 * (ν - 1) + (μ - 1) := by
          simp only [Gen13.code]; rw [ite_eq_right hA]; exact ite_eq_left hB
        obtain ⟨rfl, ht, hν, hμ⟩ := hB
        rw [hcode]
        refine ⟨fun arr => ?_, fun arr v => ?_⟩
        · rw [(pair_own_partner t μ ν arr[u]! arr hμ hν).1, (pair_own_partner t μ ν 0 arr hμ hν).2]
          simp only [Gen3.Factor.eval]
          exact Nat.mul_comm _ _
        · rw [(pair_own_partner t μ ν v arr hμ hν).1, (pair_own_partner t μ ν 0 arr hμ hν).2]
          simp only [Gen5.evalAt, ht, ↓reduceIte]
          exact Nat.mul_comm _ _
      · simp only [Gen13.code] at hc
        rw [ite_eq_right hA, ite_eq_right hB] at hc
        exact absurd rfl hc
  | general rs => simp [Gen13.code] at hc

theorem setBounds13_eq (C : Gen3.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (lo hi : Array Nat) (s loS hiS : Nat) (ks : Array Nat) (fs : Array Gen3.Factor)
    (rs : FloatArray) (hfs : fs.size = ks.size) : ∀ i, i ≤ ks.size → ∀ lower tree pending,
    Gen13.setBounds C P hP2 lo hi s loS hiS lo[s]! hi[s]! ks (fs.map (Gen13.code s)) fs rs i
        lower tree pending =
      Gen12.setBounds C P hP2 lo hi s loS hiS ks fs rs i lower tree pending := by
  intro i
  induction i with
  | zero => intro _ lower tree pending; rfl
  | succ i ih =>
    intro hi' lower tree pending
    have hn : ks.size - (i + 1) < fs.size := by omega
    have hcn : (fs.map (Gen13.code s))[ks.size - (i + 1)]! =
        Gen13.code s fs[ks.size - (i + 1)]! := by
      rw [getElem!_pos (fs.map (Gen13.code s)) _ (by simp; omega), Array.getElem_map,
        getElem!_pos fs _ hn]
    have ih' := ih (by omega)
    rw [Gen13.setBounds, Gen12.setBounds]
    simp only [hcn]
    by_cases hc : Gen13.code s fs[ks.size - (i + 1)]! = 2
    · simp only [hc, ↓reduceIte, ih']
    · simp only [hc, ↓reduceIte, ← (code_eval s _ hc).1 lo, ← (code_eval s _ hc).1 hi,
        ← (code_eval s _ hc).2 lo loS, ← (code_eval s _ hc).2 hi hiS, ih']

lemma codesOf_get (C : Gen5.Compiled) (s : Nat) :
    (Gen13.codesOf C)[s]! = (C.depFactors[s]!).map (Gen13.code s) := by
  unfold Gen13.codesOf
  by_cases hs : s < C.depFactors.size
  · rw [getElem!_pos (C.depFactors.mapIdx fun s fs => fs.map (Gen13.code s)) s (by simp; exact hs),
      getElem!_pos C.depFactors s hs, Array.getElem_mapIdx]
  · rw [getElem!_neg (C.depFactors.mapIdx fun s fs => fs.map (Gen13.code s)) s
      (by simp; omega), getElem!_neg C.depFactors s (by omega)]
    show (#[] : Array Nat) = Array.map (Gen13.code s) #[]
    exact Array.map_empty.symm

lemma gen5_depFactors_size (net : Network Float) (s : Nat) :
    ((Gen5.compile net).depFactors[s]!).size = ((Gen5.compile net).base.deps[s]!).size := by
  simp only [Gen5.compile]
  by_cases hs : s < (Gen3.compile net).deps.size
  · rw [getElem!_pos ((Gen3.compile net).deps.map
        (·.map fun k => Gen3.Factor.compile net.reactions[k]!.reactants)) s (by simp; exact hs),
      getElem!_pos (Gen3.compile net).deps s hs, Array.getElem_map, Array.size_map]
  · rw [getElem!_neg ((Gen3.compile net).deps.map
        (·.map fun k => Gen3.Factor.compile net.reactions[k]!.reactants)) s (by simp; omega),
      getElem!_neg (Gen3.compile net).deps s (by omega)]
    rfl

theorem rebracket13_eq (C : Gen5.Compiled)
    (hC : ∀ s : Nat, (C.depFactors[s]!).size = (C.base.deps[s]!).size) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (pop : Array Nat) (c : Cache) (s : Nat) :
    Gen13.rebracket C (Gen13.codesOf C) P hP2 pop c s = Gen12.rebracket C P hP2 pop c s := by
  simp only [Gen13.rebracket, Gen12.rebracket, codesOf_get,
    setBounds13_eq _ _ _ _ _ _ _ _ _ _ _ (hC s) _ (Nat.le_refl _)]

theorem fire13_eq (C : Gen6.Compiled)
    (hC : ∀ s : Nat, (C.gen5.depFactors[s]!).size = (C.gen5.base.deps[s]!).size) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms pop : Array Nat) (c : Cache) (j : Nat) :
    Gen13.fire C (Gen13.codesOf C.gen5) P hP2 ms pop c j = Gen12.fire C P hP2 ms pop c j := by
  simp only [Gen13.fire, Gen12.fire, Gen13.refresh, Gen12.refresh, rebracket13_eq _ hC]

theorem descendW13_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (depth : Nat) (hPd : P.toNat = 2 ^ depth) :
    ∀ n i (k : USize) (hk0 : 0 < k.toNat) (x : Float), i + n = depth → 2 ^ i ≤ k.toNat →
      k.toNat < 2 ^ (i + 1) →
      (Gen13.descendW tree P hP hP2 k hk0 x).toNat = Gen1.descend tree n k.toNat x := by
  intro n
  induction n with
  | zero =>
    intro i k hk0 x hi hlo _
    obtain rfl : i = depth := by omega
    have hkP : ¬ k < P := by
      intro h
      have : k.toNat < P.toNat := h
      omega
    rw [Gen13.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
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
    rw [Gen13.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
    simp only [Gen1.descend, floatArray_uget_eq, h2]
    split
    · rw [← h2]
      exact ih (i + 1) (2 * k) _ x (by omega) (by rw [h2]; omega) (by rw [h2]; omega)
    · rw [show 2 * k.toNat + 1 = (2 * k + 1).toNat from h21.symm]
      exact ih (i + 1) (2 * k + 1) _ _ (by omega) (by rw [h21]; omega) (by rw [h21]; omega)

theorem descendAt13_eq (tree : FloatArray) (depth : Nat) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ depth) (x : Float) :
    Gen13.descendAt tree depth P hP2 x = Gen1.descend tree depth 1 x := by
  unfold Gen13.descendAt
  split
  · have h1 : (1 : USize).toNat = 1 := by
      rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
    rw [descendW13_eq tree P _ hP2 depth hPd depth 0 1 _ x (by omega) (by rw [h1]; simp)
      (by rw [h1]; simp), h1]
  · rfl

/-- Generation 13's driver from one proposal on is generation 12's, given the statement for
the next event. -/
theorem run13_eq_of (C : Gen6.Compiled)
    (hC : ∀ s : Nat, (C.gen5.depFactors[s]!).size = (C.gen5.base.deps[s]!).size) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float)
    (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen13.run C (Gen13.codesOf C.gen5) C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel
          pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen12.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total elapsed
          s0 s1 s2 s3 count trace) :
    ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen13.run C (Gen13.codesOf C.gen5) C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel
          pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen12.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen13.run.eq_1, Gen12.run.eq_1]
  | succ pf ih =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen13.run.eq_2, Gen12.run.eq_2]
    simp only [descendAt13_eq _ _ _ _ hPd, descendAt12_eq _ _ _ _ hPd, fire13_eq _ hC, ih]
    cases fuel with
    | zero => rfl
    | succ f => simp only [hnext f rfl]

theorem gen13_run_eq (C : Gen6.Compiled)
    (hC : ∀ s : Nat, (C.gen5.depFactors[s]!).size = (C.gen5.base.deps[s]!).size) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float)
    (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen13.run C (Gen13.codesOf C.gen5) C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel
          pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen12.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P hP2
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero => exact run13_eq_of C hC P hP2 hPd horizon save cap 0 (fun f h => absurd h (by omega))
  | succ f ih =>
    exact run13_eq_of C hC P hP2 hPd horizon save cap (f + 1) (fun f' h => by cases h; exact ih)

theorem start13_eq (C : Gen6.Compiled) (hC : C.gen5.base.leaves = 2 ^ C.gen5.base.depth)
    (hD : ∀ s : Nat, (C.gen5.depFactors[s]!).size = (C.gen5.base.deps[s]!).size)
    (horizon : Float) (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float)
    (rng : Xoshiro) (count : Nat) (trace : Array (Float × State)) :
    Gen13.start C (Gen13.codesOf C.gen5) horizon save cap fuel pop c now rng count trace =
      Gen12.start C horizon save cap fuel pop c now rng count trace := by
  unfold Gen13.start Gen12.start
  split
  · rename_i h
    have hPd : C.gen5.base.leaves.toUSize.toNat = 2 ^ C.gen5.base.depth := by
      rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega), hC]
    simp only [gen13_run_eq C hD _ _ hPd]
  · rfl

/-- Generation 13 returns what generation 12 returns, on every network and input. -/
theorem gen13_eq_gen12 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen13.simulate net initial start horizon rng maxEvents save cap =
      Gen12.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen13.simulate Gen12.simulate
  simp only [start13_eq _ (gen6_compile_leaves net) (gen5_depFactors_size net)]

/-- **Generation 13 is the specification.** For every network whose reactant species are in
range and every input, generation 13 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen13_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen13.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen13_eq_gen12, gen12_simulate_eq net hwf]

end JumpProcessesLean.Proofs
