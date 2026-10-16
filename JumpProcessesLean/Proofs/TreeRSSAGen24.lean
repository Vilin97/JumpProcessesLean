import JumpProcessesLean.Proofs.TreeRSSAGen23
import JumpProcessesLean.TreeRSSA.Gen24

/-!
# Generation 24 is generation 23, hence the specification

Generation 24's descent ends in a pair of levels computed as `4k + c`; it returns the leaf of
the word descent (`Gen24.descend2_eq`), and the rest of its driver is generation 23's, so it
agrees with generation 19's driver as generation 23's does (`gen24_run_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)
open JumpProcessesLean.TreeRSSA.Gen7 (floatInf floatNegInf)

theorem descendW24_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      Gen24.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x := by
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [Gen24.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
      Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
  | succ m ih =>
    intro k hk0 x hm
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [Gen24.descendW, dite_eq_left_of_eq_true (eq_true hkP),
        Gen19.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega)
    · rw [Gen24.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
        Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]

theorem descendW24_eq' (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) :
    Gen24.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x :=
  descendW24_eq tree P hP hP2 _ k hk0 x le_rfl

theorem descendG24_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (hL : Gen22.Level P D 1) (x : Float) :
    (if 9 ≤ D then Gen24.descend2 tree P hP hP2 D 1 hL x
      else Gen24.descendW tree P hP hP2 1 Gen11.usize_one_pos x) =
      Gen19.descendW tree P hP hP2 1 Gen11.usize_one_pos x := by
  split
  · rw [Gen24.descend2_eq tree P hP hP2 _ D 1 hL Gen11.usize_one_pos x (Nat.le_refl _)]
    exact descendW24_eq' tree P hP hP2 1 Gen11.usize_one_pos x
  · exact descendW24_eq' tree P hP hP2 1 Gen11.usize_one_pos x

/-! ## The driver -/

theorem run24_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (hL : Gen22.Level P D 1) (rxs : Array Gen21.RxW)
    (hR : Gen21.RxOK W rates numRx.toNat rxs) (horizon : Float) (save : Bool) (cap : USize)
    (fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = f →
      Gen24.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
      evW.toNat = fuel → prW.toNat = prFuel →
      Gen24.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have h0 : prW = 0 := USize.toNat_inj.mp (by rw [hpr]; rfl)
    rw [Gen24.run, dite_eq_left h0, Gen19.run, dite_eq_left h0]
  | succ pf ih =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have hT := tree_usize P hP2 c.tree hc.2.2
    have hU := hB.nU
    have hm := hB.changes
    have hpopU : pop.size < USize.size := by omega
    have ih' : ∀ pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
        Gen24.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
            (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
          Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW (prW - 1)
            pop c now total elapsed s0 s1 s2 s3 count trace :=
      fun pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
        ih evW (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
          (usize_pred_toNat hpr)
    by_cases he : evW = 0
    · rw [Gen24.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_left he, descendG24_eq, rx_rate hR, rx_eval hR]
      simp only [uget_fget, ih', dite_eq_ite, ite_false_not]
    · have hev0 : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
      obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hn' : ∀ (prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
          Gen24.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
              (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
            Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap (evW - 1)
              prW pop c now total elapsed s0 s1 s2 s3 count trace :=
        fun prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
          hnext f hf (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace
            (by rw [Gen16.pred_toNat evW he]; omega)
      rw [Gen24.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_right he, descendG24_eq, rx_rate hR, rx_eval hR, applyR22_eq,
        rx_apply hR hm (hpopU := hpopU), rx_small hR hm, rx_refresh22 hR hm]
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

/-- Generation 24's driver returns what generation 19's returns. -/
theorem gen24_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (hL : Gen22.Level P D 1) (rxs : Array Gen21.RxW)
    (hR : Gen21.RxOK W rates numRx.toNat rxs) (horizon : Float) (save : Bool) (cap : USize) :
    ∀ fuel prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize)
      trace, evW.toNat = fuel → prW.toNat = prFuel →
      Gen24.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run24_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    refine run24_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
      (f + 1) ?_
    intro f' hf' evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
    obtain rfl : f' = f := by omega
    exact ih prW.toNat evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev rfl

theorem start24_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (count : Nat) (trace : Array (Float × State)) :
    Gen24.start C codes horizon save cap fuel pop c now rng count trace =
      Gen23.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen24.start
  dsimp only
  split
  · rename_i h
    split
    · rename_i hs
      unfold Gen23.start
      dsimp only
      rw [dite_eq_left h, dite_eq_left hs]
      exact (gen24_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).trans
        (gen23_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).symm
    · rfl
  · rfl

/-- Generation 24 returns what generation 23 returns, on every network and input. -/
theorem gen24_eq_gen23 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen24.simulate net initial start horizon rng maxEvents save cap =
      Gen23.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen24.simulate Gen23.simulate
  simp only [start24_eq]

/-- **Generation 24 is the specification.** For every network whose reactant species are in
range and every input, generation 24 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen24_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen24.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen24_eq_gen23, gen23_simulate_eq net hwf]

end JumpProcessesLean.Proofs
