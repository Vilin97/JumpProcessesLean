import JumpProcessesLean.Proofs.TreeRSSAGen24
import JumpProcessesLean.TreeRSSA.Gen25

/-!
# Generation 25 is generation 24, hence the specification

Generation 25 reads the cache's brackets inside each firing step and builds states and the
fallback cache in calls, so that no projection of the cache stays live across the firing's join
points. These are definitional rewrites (`applyRC_eq`, `stateOfV`, `toCacheV`), and the rest of
its driver is generation 24's (`gen25_run_eq`). Its start tests generation 24's conditions at once
and otherwise calls generation 21's start, as generations 22 to 24 do (`start25_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)
open JumpProcessesLean.TreeRSSA.Gen7 (floatInf floatNegInf)

theorem descendW25_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      Gen25.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x := by
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [Gen25.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
      Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
  | succ m ih =>
    intro k hk0 x hm
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [Gen25.descendW, dite_eq_left_of_eq_true (eq_true hkP),
        Gen19.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega)
    · rw [Gen25.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
        Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]

theorem descendW25_eq' (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) :
    Gen25.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x :=
  descendW25_eq tree P hP hP2 _ k hk0 x le_rfl

theorem descendG25_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (hL : Gen22.Level P D 1) (x : Float) :
    (if 9 ≤ D then Gen25.descend2 tree P hP hP2 D 1 hL x
      else Gen25.descendW tree P hP hP2 1 Gen11.usize_one_pos x) =
      Gen19.descendW tree P hP hP2 1 Gen11.usize_one_pos x := by
  split
  · rw [Gen25.descend2_eq tree P hP hP2 _ D 1 hL Gen11.usize_one_pos x (Nat.le_refl _)]
    exact descendW25_eq' tree P hP hP2 1 Gen11.usize_one_pos x
  · exact descendW25_eq' tree P hP hP2 1 Gen11.usize_one_pos x

/-! ## The driver -/

theorem run25_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (hL : Gen22.Level P D 1) (rxs : Array Gen21.RxW)
    (hR : Gen21.RxOK W rates numRx.toNat rxs) (horizon : Float) (save : Bool) (cap : USize)
    (fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = f →
      Gen25.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
      evW.toNat = fuel → prW.toNat = prFuel →
      Gen25.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have h0 : prW = 0 := USize.toNat_inj.mp (by rw [hpr]; rfl)
    rw [Gen25.run, dite_eq_left h0, Gen19.run, dite_eq_left h0]
  | succ pf ih =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have hT := tree_usize P hP2 c.tree hc.2.2
    have hU := hB.nU
    have hm := hB.changes
    have hpopU : pop.size < USize.size := by omega
    have ih' : ∀ pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
        Gen25.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
            (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
          Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW (prW - 1)
            pop c now total elapsed s0 s1 s2 s3 count trace :=
      fun pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
        ih evW (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
          (usize_pred_toNat hpr)
    by_cases he : evW = 0
    · rw [Gen25.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_left he, descendG25_eq, rx_rate hR, rx_eval hR, Gen25.stateOfV]
      simp only [uget_fget, ih', dite_eq_ite, ite_false_not]
    · have hev0 : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
      obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hn' : ∀ (prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
          Gen25.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
              (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
            Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap (evW - 1)
              prW pop c now total elapsed s0 s1 s2 s3 count trace :=
        fun prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
          hnext f hf (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace
            (by rw [Gen16.pred_toNat evW he]; omega)
      rw [Gen25.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_right he, descendG25_eq, rx_rate hR, rx_eval hR, Gen25.applyRC_eq,
        applyR22_eq, rx_apply hR hm (hpopU := hpopU), rx_small hR hm, rx_refresh22 hR hm,
        Gen25.stateOfV, Gen25.toCacheV]
      simp only [uget_fget, ih', hn', Gen18.cget, dite_eq_ite, ite_false_not]
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      exact dite_ite_eq rfl (fun _ => rfl) (fun _ => rfl)

/-- Generation 25's driver returns what generation 19's returns. -/
theorem gen25_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (hL : Gen22.Level P D 1) (rxs : Array Gen21.RxW)
    (hR : Gen21.RxOK W rates numRx.toNat rxs) (horizon : Float) (save : Bool) (cap : USize) :
    ∀ fuel prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize)
      trace, evW.toNat = fuel → prW.toNat = prFuel →
      Gen25.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run25_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    refine run25_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
      (f + 1) ?_
    intro f' hf' evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
    obtain rfl : f' = f := by omega
    exact ih prW.toNat evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev rfl

/-- When the conditions of generation 24's start fail, generations 22 to 24 all return
generation 21's start: their starts test the same conditions. -/
theorem start25_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (count : Nat) (trace : Array (Float × State)) :
    Gen25.start C codes horizon save cap fuel pop c now rng count trace =
      Gen24.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen25.start Gen24.start
  dsimp only
  split
  · rename_i h
    rw [dite_eq_left h.1, dite_eq_left h.2]
    exact (gen25_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).trans (gen24_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).symm
  · rename_i h
    have h22 : Gen22.start C codes horizon save cap fuel pop c now rng count trace =
        Gen21.start C codes horizon save cap fuel pop c now rng count trace := by
      unfold Gen22.start
      dsimp only
      split
      · split
        · exact (h ⟨‹_›, ‹_›⟩).elim
        · rfl
      · rfl
    have h23 : Gen23.start C codes horizon save cap fuel pop c now rng count trace =
        Gen21.start C codes horizon save cap fuel pop c now rng count trace := by
      unfold Gen23.start
      dsimp only
      split
      · split
        · exact (h ⟨‹_›, ‹_›⟩).elim
        · exact h22
      · exact h22
    split
    · split
      · exact (h ⟨‹_›, ‹_›⟩).elim
      · exact h23.symm
    · exact h23.symm

/-- Generation 25 returns what generation 24 returns, on every network and input. -/
theorem gen25_eq_gen24 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen25.simulate net initial start horizon rng maxEvents save cap =
      Gen24.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen25.simulate Gen24.simulate
  simp only [start25_eq]

/-- **Generation 25 is the specification.** For every network whose reactant species are in
range and every input, generation 25 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen25_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen25.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen25_eq_gen24, gen24_simulate_eq net hwf]

end JumpProcessesLean.Proofs
