import JumpProcessesLean.Proofs.TreeRSSAGen21
import JumpProcessesLean.TreeRSSA.Gen22

/-!
# Generation 22 is generation 21, hence the specification

The two-level descent reads the nodes the one-level descent reads and takes the same branches
(`descend2_eq`), the module's walks and refreshes are generation 21's (`fixUntilR_eq`,
`setBoundsR22_eq`, `refreshFromR22_eq`), and its firing step is generation 21's. The driver
then agrees with generation 19's as generation 21's does (`gen22_run_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)
open JumpProcessesLean.TreeRSSA.Gen7 (floatInf floatNegInf)

theorem descendW22_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      Gen22.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x := by
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [Gen22.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
      Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
  | succ m ih =>
    intro k hk0 x hm
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [Gen22.descendW, dite_eq_left_of_eq_true (eq_true hkP),
        Gen19.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega)
    · rw [Gen22.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
        Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]

theorem descendW22_eq' (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) :
    Gen22.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x :=
  descendW22_eq tree P hP hP2 _ k hk0 x le_rfl

theorem descendG22_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (hL : Gen22.Level P D 1) (x : Float) :
    (if 12 ≤ D then Gen22.descend2 tree P hP hP2 D 1 hL x
      else Gen22.descendW tree P hP hP2 1 Gen11.usize_one_pos x) =
      Gen19.descendW tree P hP hP2 1 Gen11.usize_one_pos x := by
  split
  · rw [Gen22.descend2_eq tree P hP hP2 _ D 1 hL Gen11.usize_one_pos x (Nat.le_refl _)]
    exact descendW22_eq' tree P hP hP2 1 Gen11.usize_one_pos x
  · exact descendW22_eq' tree P hP hP2 1 Gen11.usize_one_pos x

/-! ## Walks and refreshes -/

theorem fixUntilR_eq (P : USize) : ∀ (m : Nat) (n : USize), n.toNat = m →
    ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float),
      Gen22.fixUntilR P n tree hP node hn other v = Gen16.fixUntilGo P n tree hP node hn other v := by
  intro m
  induction m with
  | zero =>
    intro n hm tree hP node hn other v
    have hz : n = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [Gen22.fixUntilR, dite_eq_left hz, Gen16.fixUntilGo, dite_eq_left hz]
  | succ m ih =>
    intro n hm tree hP node hn other v
    have hz : n ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [Gen22.fixUntilR, dite_eq_right hz, Gen16.fixUntilGo, dite_eq_right hz]
    simp only [ih (n - 1) (by rw [Gen16.pred_toNat n hz]; omega)]

theorem fixPathR_eq (P : USize) : ∀ (m : Nat) (n : USize), n.toNat = m →
    ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (v : Float),
      Gen22.fixPathR P n tree hP node hn v = Gen16.fixPathGo P n tree hP node hn v := by
  intro m
  induction m with
  | zero =>
    intro n hm tree hP node hn v
    have hz : n = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [Gen22.fixPathR, dite_eq_left hz, Gen16.fixPathGo, dite_eq_left hz]
  | succ m ih =>
    intro n hm tree hP node hn v
    have hz : n ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [Gen22.fixPathR, dite_eq_right hz, Gen16.fixPathGo, dite_eq_right hz]
    simp only [ih (n - 1) (by rw [Gen16.pred_toNat n hz]; omega)]

theorem setBoundsR22_eq (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (nW : USize)
    (hi : FloatArray) (hhi : nW.toNat ≤ hi.size) (h0 h1 g0 g1 : Float) (ds : Array Gen18.DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat) :
    ∀ m (i : USize), ds.size - i.toNat = m → ∀ (tree : FloatArray)
      (htree : 2 * P.toNat ≤ tree.size) (pending : USize) hpend,
      Gen22.setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend =
        Gen21.setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend := by
  intro m
  induction m with
  | zero =>
    intro i hm tree htree pending hpend
    have hge : ¬ i < ds.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize ds i h; omega
    rw [Gen22.setBoundsR, dite_eq_right hge, Gen21.setBoundsR, dite_eq_right hge]
    simp only [fixPathR_eq P _ D rfl]
  | succ m ih =>
    intro i hm tree htree pending hpend
    by_cases h : i < ds.usize
    · have hs := Gen15.succ_toNat_of_lt_usize ds i h
      rw [Gen22.setBoundsR, dite_eq_left h, Gen21.setBoundsR, dite_eq_left h]
      simp only [ih (i + 1) (by omega), fixUntilR_eq P _ D rfl]
    · rw [Gen22.setBoundsR, dite_eq_right h, Gen21.setBoundsR, dite_eq_right h]
      simp only [fixPathR_eq P _ D rfl]

theorem rebracketR22_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (c : Gen19.CacheV) (hc : Gen20.Sized nW P c)
    (s : USize) (hs : s.toNat < nW.toNat) :
    Gen22.rebracketR W P hP2 D nW numRx rates hB pop hpop c hc s hs =
      Gen19.rebracketV W P P hP2 D pop c s := by
  rw [← rebracketR_eq W P hP2 D nW numRx rates hB pop hpop c hc s hs]
  simp only [Gen22.rebracketR, Gen21.rebracketR]
  rw [setBoundsR22_eq _ _ _ _ _ _ _ _ _ _ _ _ _ 0 rfl]

theorem refresh1_22_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (s : USize) (hs : s.toNat < nW.toNat)
    (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) :
    Gen22.refresh1 W P hP2 D nW numRx rates hB pop hpop s hs c hc =
      if Gen18.staleW (Gen18.cget W.ms s) (Gen18.cget pop s) (Gen18.cget c.lo s)
          (Gen18.cget c.hi s) then Gen19.rebracketV W P P hP2 D pop c s else c := by
  have hms := hB.ms
  have h1 := hc.1
  have h2 := hc.2.1
  simp only [Gen22.refresh1]
  rw [cget_uget W.ms _ (by omega), cget_uget pop _ (by omega), cget_uget c.lo _ (by omega),
    cget_uget c.hi _ (by omega), rebracketR22_eq]

theorem refreshFromR22_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (chs : Array Gen18.ChangeW) (r : Gen21.RxW) (hch : ChsAt chs r)
    (h0 : r.c0.toNat < nW.toNat) (h1 : r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) :
    Gen22.refreshFromR W P hP2 D nW numRx rates hB r h0 h1 h2 pop hpop c hc =
      Gen19.refreshFromV W P P hP2 D chs pop 0 c := by
  have hsz := hch.size
  have hcs : chs.size < USize.size := by
    have : chs.size ≤ 3 := by rw [hsz]; split <;> omega
    have hU : 4 ≤ USize.size := by
      have hsz' : USize.size = 2 ^ System.Platform.numBits := rfl
      rcases System.Platform.numBits_eq with h | h <;> rw [hsz', h] <;> decide
    omega
  have hu := usize_toNat_of_small chs hcs
  have hs2 : 2 ≤ chs.size := by rw [hsz]; split <;> omega
  have i0 : (0 : USize) < chs.usize := by
    show (0 : USize).toNat < chs.usize.toNat; rw [hu, USize.toNat_zero]; omega
  have t1 : ((0 : USize) + 1).toNat = 1 := Gen15.succ_toNat_of_lt_usize chs 0 i0
  have i1 : (0 : USize) + 1 < chs.usize := by
    show ((0 : USize) + 1).toNat < chs.usize.toNat; rw [t1, hu]; omega
  have t2 : ((0 : USize) + 1 + 1).toNat = 2 := by rw [Gen15.succ_toNat_of_lt_usize chs _ i1, t1]
  have e0 : chs[(0 : USize).toNat]'(Gen15.lt_size_of_lt_usize chs 0 i0) = ⟨r.c0, r.add0, r.a0⟩ :=
    hch.ch0 _
  have e1 : chs[((0 : USize) + 1).toNat]'(Gen15.lt_size_of_lt_usize chs _ i1) =
      ⟨r.c1, r.add1, r.a1⟩ := by
    have := hch.ch1 (by omega)
    simp only [t1]
    exact this
  rw [refreshFromV_step W P P hP2 D chs pop 0 c i0 _ e0,
    refreshFromV_step W P P hP2 D chs pop _ _ i1 _ e1]
  simp only [Gen22.refreshFromR, refresh1_22_eq]
  by_cases h3 : r.three = true
  · have hs3 : chs.size = 3 := by rw [hsz, ite_eq_left h3]
    have i2 : (0 : USize) + 1 + 1 < chs.usize := by
      show ((0 : USize) + 1 + 1).toNat < chs.usize.toNat; rw [t2, hu]; omega
    have t3 : ((0 : USize) + 1 + 1 + 1).toNat = 3 := by
      rw [Gen15.succ_toNat_of_lt_usize chs _ i2, t2]
    have e2 : chs[((0 : USize) + 1 + 1).toNat]'(Gen15.lt_size_of_lt_usize chs _ i2) =
        ⟨r.c2, r.add2, r.a2⟩ := by
      have := hch.ch2 h3 (by omega)
      simp only [t2]
      exact this
    have i3 : ¬ (0 : USize) + 1 + 1 + 1 < chs.usize := by
      show ¬ ((0 : USize) + 1 + 1 + 1).toNat < chs.usize.toNat; rw [t3, hu]; omega
    rw [refreshFromV_step W P P hP2 D chs pop _ _ i2 _ e2, refreshFromV_end W P P hP2 D chs pop _ _ i3]
    simp only [h3, dite_true]
  · have h3' : r.three = false := by simpa using h3
    have hs3 : chs.size = 2 := by rw [hsz, ite_eq_right (by simp [h3'])]
    have i2 : ¬ (0 : USize) + 1 + 1 < chs.usize := by
      show ¬ ((0 : USize) + 1 + 1).toNat < chs.usize.toNat; rw [t2, hu]; omega
    rw [refreshFromV_end W P P hP2 D chs pop _ _ i2]
    simp only [h3', Bool.false_eq_true, dite_false]

theorem applyR22_eq (r : Gen21.RxW) (nW : USize) (h0 : r.c0.toNat < nW.toNat)
    (h1 : r.c1.toNat < nW.toNat) (h2 : r.three = true → r.c2.toNat < nW.toNat)
    (ms lo hi : FloatArray) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) (pop : FloatArray) (hpop : nW.toNat < pop.size) :
    Gen22.applyR r nW h0 h1 h2 ms lo hi hms hlo hhi pop hpop =
      Gen21.applyR r nW h0 h1 h2 ms lo hi hms hlo hhi pop hpop := rfl

theorem rx_refresh22 {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen21.RxW}
    (hR : Gen21.RxOK W rates m rxs) (hm : m ≤ W.changes.size) (j : USize)
    (h : j.toNat < rxs.size) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (hB : Gen20.Bounds W nW P numRx rates)
    (h0 : (rxs.uget j h).c0.toNat < nW.toNat) (h1 : (rxs.uget j h).c1.toNat < nW.toNat)
    (h2 : (rxs.uget j h).three = true → (rxs.uget j h).c2.toNat < nW.toNat) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) :
    Gen22.refreshFromR W P hP2 D nW numRx rates hB (rxs.uget j h) h0 h1 h2 pop hpop c hc =
      Gen19.refreshFromV W P P hP2 D (Gen17.aget W.changes j) pop 0 c := by
  obtain ⟨e, hch⟩ := rx_chs hR hm j h
  rw [e]
  exact refreshFromR22_eq W P hP2 D nW numRx rates hB _ _ hch h0 h1 h2 pop hpop c hc

/-! ## The driver -/

theorem run22_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (hL : Gen22.Level P D 1) (rxs : Array Gen21.RxW)
    (hR : Gen21.RxOK W rates numRx.toNat rxs) (horizon : Float) (save : Bool) (cap : USize)
    (fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = f →
      Gen22.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
      evW.toNat = fuel → prW.toNat = prFuel →
      Gen22.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have h0 : prW = 0 := USize.toNat_inj.mp (by rw [hpr]; rfl)
    rw [Gen22.run, dite_eq_left h0, Gen19.run, dite_eq_left h0]
  | succ pf ih =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have hT := tree_usize P hP2 c.tree hc.2.2
    have hU := hB.nU
    have hm := hB.changes
    have hpopU : pop.size < USize.size := by omega
    have ih' : ∀ pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
        Gen22.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
            (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
          Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW (prW - 1)
            pop c now total elapsed s0 s1 s2 s3 count trace :=
      fun pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
        ih evW (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
          (usize_pred_toNat hpr)
    by_cases he : evW = 0
    · rw [Gen22.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_left he, descendG22_eq, rx_rate hR, rx_eval hR]
      simp only [uget_fget, ih', dite_eq_ite, ite_false_not]
    · have hev0 : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
      obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hn' : ∀ (prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
          Gen22.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
              (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
            Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap (evW - 1)
              prW pop c now total elapsed s0 s1 s2 s3 count trace :=
        fun prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
          hnext f hf (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace
            (by rw [Gen16.pred_toNat evW he]; omega)
      rw [Gen22.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_right he, descendG22_eq, rx_rate hR, rx_eval hR, applyR22_eq,
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

/-- Generation 22's driver returns what generation 19's returns. -/
theorem gen22_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (hL : Gen22.Level P D 1) (rxs : Array Gen21.RxW)
    (hR : Gen21.RxOK W rates numRx.toNat rxs) (horizon : Float) (save : Bool) (cap : USize) :
    ∀ fuel prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize)
      trace, evW.toNat = fuel → prW.toNat = prFuel →
      Gen22.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run22_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    refine run22_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
      (f + 1) ?_
    intro f' hf' evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
    obtain rfl : f' = f := by omega
    exact ih prW.toNat evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev rfl

theorem start22_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (count : Nat) (trace : Array (Float × State)) :
    Gen22.start C codes horizon save cap fuel pop c now rng count trace =
      Gen21.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen22.start
  dsimp only
  split
  · rename_i h
    split
    · rename_i hs
      unfold Gen21.start
      dsimp only
      split
      · split
        · exact (gen22_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).trans
            (gen21_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).symm
        · rename_i hs21
          exact (hs21 ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1,
            hs.2.2.2.2.2.2.1⟩).elim
      · rename_i h21
        exact (h21 h).elim
    · rfl
  · rfl

/-- Generation 22 returns what generation 21 returns, on every network and input. -/
theorem gen22_eq_gen21 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen22.simulate net initial start horizon rng maxEvents save cap =
      Gen21.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen22.simulate Gen21.simulate
  simp only [start22_eq]

/-- **Generation 22 is the specification.** For every network whose reactant species are in
range and every input, generation 22 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen22_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen22.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen22_eq_gen21, gen21_simulate_eq net hwf]

end JumpProcessesLean.Proofs
