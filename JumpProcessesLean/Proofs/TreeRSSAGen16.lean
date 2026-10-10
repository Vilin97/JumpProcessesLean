import JumpProcessesLean.Proofs.TreeRSSAGen15
import JumpProcessesLean.TreeRSSA.Gen16

/-!
# Generation 16 is generation 15, hence the specification

The machine-word path walks are generation 12's with their fuel read as a natural number
(`fixUntilGo16_eq`, `fixPathGo16_eq`). The machine-word refresh visits the dependents in
generation 13's order; with the refreshed species' powers precomputed, its test of a changed
bound is generation 13's, since `a p = b p` iff `a = b` or `p = 0` (`mul_eq_ite`), and it
writes the same products (`setBounds16_eq`). So generation 16's refresh, firing and driver are
generation 15's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

lemma usize_eq_zero_of_toNat {n : USize} (h : n.toNat = 0) : n = 0 :=
  USize.toNat_inj.mp (by rw [h]; rfl)

theorem fixUntilGo16_eq (P : USize) : ∀ m (n : USize), n.toNat = m → ∀ tree hP node hn other v,
    Gen16.fixUntilGo P n tree hP node hn other v = Gen12.fixUntilGo P m tree hP node hn other v := by
  intro m
  induction m with
  | zero =>
    intro n hn0 tree hP node hn other v
    rw [Gen16.fixUntilGo, dite_eq_left_of_eq_true (eq_true (usize_eq_zero_of_toNat hn0))]
    rfl
  | succ m ih =>
    intro n hnm tree hP node hn other v
    have hz : n ≠ 0 := fun h => by rw [h] at hnm; simp at hnm
    rw [Gen16.fixUntilGo, dite_eq_right_iff.mpr (fun h => absurd h hz), Gen12.fixUntilGo]
    dsimp only
    split
    · rfl
    · exact ih (n - 1) (by rw [Gen16.pred_toNat n hz]; omega) _ _ _ _ _ _

theorem fixPathGo16_eq (P : USize) : ∀ m (n : USize), n.toNat = m → ∀ tree hP node hn v,
    Gen16.fixPathGo P n tree hP node hn v = Gen12.fixPathGo P m tree hP node hn v := by
  intro m
  induction m with
  | zero =>
    intro n hn0 tree hP node hn v
    rw [Gen16.fixPathGo, dite_eq_left_of_eq_true (eq_true (usize_eq_zero_of_toNat hn0))]
    rfl
  | succ m ih =>
    intro n hnm tree hP node hn v
    have hz : n ≠ 0 := fun h => by rw [h] at hnm; simp at hnm
    rw [Gen16.fixPathGo, dite_eq_right_iff.mpr (fun h => absurd h hz), Gen12.fixPathGo]
    exact ih (n - 1) (by rw [Gen16.pred_toNat n hz]; omega) _ _ _ _ _

theorem fixUntilAt16_eq (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray)
    (depth : Nat) (D : USize) (node other : Nat) :
    Gen16.fixUntilAt P hP2 tree depth D node other = Gen3.fixUntil tree depth node other := by
  unfold Gen16.fixUntilAt
  split
  · rename_i h
    rw [fixUntilGo16_eq P depth D h.2.2.2, fixUntilGo_eq _ _ _ _ _ _ _ _ (floatArray_uget_eq _ _ _).symm,
      Gen12.toUSize_toNat_of_lt h.2.1 hP2, Gen12.toUSize_toNat_of_lt h.2.2.1 hP2]
  · rfl

theorem fixPathAt16_eq (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray)
    (depth : Nat) (D : USize) (node : Nat) :
    Gen16.fixPathAt P hP2 tree depth D node = Gen1.fixPath tree depth node := by
  unfold Gen16.fixPathAt
  split
  · rename_i h
    rw [fixPathGo16_eq P depth D h.2.2, fixPathGo_eq _ _ _ _ _ _ _ (floatArray_uget_eq _ _ _).symm,
      Gen12.toUSize_toNat_of_lt h.2.1 hP2]
  · rfl

lemma own_sel (c x : Nat) : (if c % 2 = 1 then x * (x - 1) else x) = Gen13.own c x := by
  unfold Gen13.own Gen13.ffb
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

lemma mul_eq_ite {β : Type} (a b p : Nat) (L X : β) :
    (if a * p = b * p then L else X) = (if a = b then L else if p = 0 then L else X) := by
  by_cases hab : a = b
  · simp [hab]
  · by_cases hp : p = 0
    · simp [hab, hp]
    · have : a * p ≠ b * p := fun h => hab (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hp) h)
      simp [hab, hp, this]

theorem setBounds16_eq (C : Gen3.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (lo hi : Array Nat) (s loS hiS : Nat)
    (ks cs : Array Nat) (fs : Array Gen3.Factor) (rs : FloatArray) (hcs : cs.size = ks.size)
    (hrs : rs.size = ks.size) (hsmall : ks.size < USize.size) :
    ∀ m (i : USize), ks.size - i.toNat = m → ∀ lower tree pending,
      Gen16.setBounds C P hP2 D lo hi s loS hiS lo[s]! (lo[s]! * (lo[s]! - 1)) loS (loS * (loS - 1))
          hi[s]! (hi[s]! * (hi[s]! - 1)) hiS (hiS * (hiS - 1)) ks cs fs rs hcs hrs i lower tree
          pending =
        Gen13.setBounds C P hP2 lo hi s loS hiS lo[s]! hi[s]! ks cs fs rs m lower tree pending := by
  intro m
  induction m with
  | zero =>
    intro i hm lower tree pending
    have hni : ¬ i < ks.usize := by
      intro h
      have := Gen15.lt_size_of_lt_usize ks i h
      omega
    rw [Gen16.setBounds, dite_eq_right_iff.mpr (fun h => absurd h hni), Gen13.setBounds]
    simp only [fixPathAt16_eq, fixPathAt_eq]
  | succ m ih =>
    intro i hm lower tree pending
    have hi' : i.toNat < ks.size := by omega
    have hlt : i < ks.usize := by
      show i.toNat < ks.usize.toNat
      rw [usize_toNat_eq ks hsmall]; exact hi'
    have hn : ks.size - (m + 1) = i.toNat := by omega
    have hnext : ks.size - (i + 1).toNat = m := by
      rw [Gen15.succ_toNat_of_lt_usize ks i hlt]; omega
    rw [Gen16.setBounds, dite_eq_left_of_eq_true (eq_true hlt), Gen13.setBounds]
    have hk : ks.uget i hi' = ks[i.toNat]! := by
      rw [getElem!_pos ks _ hi']; rfl
    have hc : cs.uget i (by rw [hcs]; exact hi') = cs[i.toNat]! := by
      rw [getElem!_pos cs _ (by rw [hcs]; exact hi')]; rfl
    have hr : rs.uget i (by rw [hrs]; exact hi') = rs.get! i.toNat := floatArray_uget_eq _ _ _
    simp only [hn, hk, hc, hr, ih (i + 1) hnext, own_sel, fixUntilAt16_eq, fixUntilAt_eq,
      mul_eq_ite]

theorem rebracket16_eq (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (pop : Array Nat) (c : Cache) (s : Nat) :
    Gen16.rebracket C codes P hP2 pop c s = Gen13.rebracket C codes P hP2 pop c s := by
  unfold Gen16.rebracket Gen13.rebracket
  dsimp only
  split
  · rename_i h
    rw [setBounds16_eq C.base P hP2 _ _ _ s _ _ _ _ _ _ h.1 h.2.1 h.2.2
      (C.base.deps[s]!).size 0 (by simp)]
  · rfl

theorem refresh16_eq (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms pop : Array Nat) (c : Cache) (s : Nat) :
    Gen16.refresh C codes P hP2 ms pop c s = Gen13.refresh C codes P hP2 ms pop c s := by
  simp only [Gen16.refresh, Gen13.refresh, rebracket16_eq]

theorem fire16_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms : Array Nat) (n : Nat) (hms : ms.size = n)
    (hval : Gen15.ValidChanges C n) (pop : Array Nat) (hpop : pop.size = n) (c : Cache)
    (hlo : c.lo.size = n) (hhi : c.hi.size = n) (j : Nat) :
    Gen16.fire C codes P hP2 ms n hms hval pop hpop c hlo hhi j =
      Gen15.fire C codes P hP2 ms n hms hval pop hpop c hlo hhi j := by
  apply Subtype.ext
  simp only [Gen16.fire, Gen15.fire, refresh16_eq]

theorem descendW16_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (depth : Nat) (hPd : P.toNat = 2 ^ depth) :
    ∀ n i (k : USize) (hk0 : 0 < k.toNat) (x : Float), i + n = depth → 2 ^ i ≤ k.toNat →
      k.toNat < 2 ^ (i + 1) →
      (Gen16.descendW tree P hP hP2 k hk0 x).toNat = Gen1.descend tree n k.toNat x := by
  intro n
  induction n with
  | zero =>
    intro i k hk0 x hi hlo _
    obtain rfl : i = depth := by omega
    have hkP : ¬ k < P := by
      intro h
      have : k.toNat < P.toNat := h
      omega
    rw [Gen16.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
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
    rw [Gen16.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
    simp only [Gen1.descend, floatArray_uget_eq, h2]
    split
    · rw [← h2]
      exact ih (i + 1) (2 * k) _ x (by omega) (by rw [h2]; omega) (by rw [h2]; omega)
    · rw [show 2 * k.toNat + 1 = (2 * k + 1).toNat from h21.symm]
      exact ih (i + 1) (2 * k + 1) _ _ (by omega) (by rw [h21]; omega) (by rw [h21]; omega)


/-- Generation 16's driver from one proposal on is generation 15's, given the statement for
the next event. -/
theorem run16_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (n : Nat)
    (hms : C.gen5.base.ms.size = n) (hval : Gen15.ValidChanges C n)
    (hsmall : ∀ j : Nat, (C.changes[j]!).size < USize.size) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float)
    (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count
      trace,
      Gen16.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel
          pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace =
        Gen15.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel
          pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace,
      Gen16.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel
          pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace =
        Gen15.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel
          pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace
    rw [Gen16.run.eq_1, Gen15.run.eq_1]
  | succ pf ih =>
    intro pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace
    rw [Gen16.run.eq_2]
    by_cases hT : 2 * P ≤ c.tree.usize
    · rw [dite_eq_left_of_eq_true (eq_true hT), Gen15.run.eq_2,
        dite_eq_left_of_eq_true (eq_true hT)]
      have h1 : (1 : USize).toNat = 1 := by
        rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
      have hd16 : ∀ x, (Gen16.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
          Gen11.usize_one_pos x).toNat = Gen1.descend c.tree C.gen5.base.depth 1 x := by
        intro x
        rw [descendW16_eq c.tree P _ hP2 C.gen5.base.depth hPd C.gen5.base.depth 0 1 _ x
          (by omega) (by rw [h1]; simp) (by rw [h1]; simp), h1]
      have hd15 : ∀ x, (Gen15.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
          Gen11.usize_one_pos x).toNat = Gen1.descend c.tree C.gen5.base.depth 1 x := by
        intro x
        rw [descendW15_eq c.tree P _ hP2 C.gen5.base.depth hPd C.gen5.base.depth 0 1 _ x
          (by omega) (by rw [h1]; simp) (by rw [h1]; simp), h1]
      simp only [hd16, hd15, ih, fire16_eq, fire15_mk C codes P hP2 _ n hms hval hsmall]
      cases fuel with
      | zero => rfl
      | succ f => simp only [hnext f rfl]
    · rw [dite_eq_right_iff.mpr (fun h => absurd h hT)]

theorem gen16_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (n : Nat)
    (hms : C.gen5.base.ms.size = n) (hval : Gen15.ValidChanges C n)
    (hsmall : ∀ j : Nat, (C.changes[j]!).size < USize.size) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float)
    (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace,
      Gen16.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel
          pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace =
        Gen15.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel
          pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run16_eq_of C codes n hms hval hsmall P hP2 hPd horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    exact run16_eq_of C codes n hms hval hsmall P hP2 hPd horizon save cap (f + 1)
      (fun f' h => by cases h; exact ih)

theorem start16_eq (C : Gen6.Compiled) (codes : Array (Array Nat))
    (hC : C.gen5.base.leaves = 2 ^ C.gen5.base.depth) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) :
    Gen16.start C codes horizon save cap fuel pop c now rng count trace =
      Gen15.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen16.start Gen15.start
  split
  · rename_i h
    have hPd : C.gen5.base.leaves.toUSize.toNat = 2 ^ C.gen5.base.depth := by
      rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega), hC]
    split
    · rename_i hs
      simp only [gen16_run_eq C codes _ rfl _ (validChanges_small hs.2.2.2) _ _ hPd]
    · rfl
  · rfl

/-- Generation 16 returns what generation 15 returns, on every network and input. -/
theorem gen16_eq_gen15 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen16.simulate net initial start horizon rng maxEvents save cap =
      Gen15.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen16.simulate Gen15.simulate
  simp only [start16_eq _ _ (gen6_compile_leaves net)]

/-- **Generation 16 is the specification.** For every network whose reactant species are in
range and every input, generation 16 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen16_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen16.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen16_eq_gen15, gen15_simulate_eq net hwf]

end JumpProcessesLean.Proofs
