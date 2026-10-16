import JumpProcessesLean.Proofs.TreeRSSAGen25
import JumpProcessesLean.TreeRSSA.Gen26

/-!
# Generation 26 is generation 25, hence the specification

Generation 26's records hold one, two or three changes; firing, the small-count test and the
refresh of a record apply its changes array in order (`applyRV_eq`, `smallV_eq`,
`refreshFromRV_eq`), which is all the driver proof needs (`gen26_run_eq`). Its start takes the
fast path on networks with reactions of one change too: there generation 25 falls through
generation 21's start to generation 20's, whose driver agrees with generation 19's as
generation 26's does (`start26_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)
open JumpProcessesLean.TreeRSSA.Gen7 (floatInf floatNegInf)

theorem descendW26_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      Gen26.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x := by
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [Gen26.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
      Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
  | succ m ih =>
    intro k hk0 x hm
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [Gen26.descendW, dite_eq_left_of_eq_true (eq_true hkP),
        Gen19.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega)
    · rw [Gen26.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
        Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]

theorem descendW26_eq' (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) :
    Gen26.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x :=
  descendW26_eq tree P hP hP2 _ k hk0 x le_rfl

theorem descendG26_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (hL : Gen22.Level P D 1) (x : Float) :
    (if 9 ≤ D then Gen26.descend2 tree P hP hP2 D 1 hL x
      else Gen26.descendW tree P hP hP2 1 Gen11.usize_one_pos x) =
      Gen19.descendW tree P hP hP2 1 Gen11.usize_one_pos x := by
  split
  · rw [Gen26.descend2_eq tree P hP hP2 _ D 1 hL Gen11.usize_one_pos x (Nat.le_refl _)]
    exact descendW26_eq' tree P hP hP2 1 Gen11.usize_one_pos x
  · exact descendW26_eq' tree P hP hP2 1 Gen11.usize_one_pos x

/-! ## Walks and refreshes -/

theorem fixUntilR26_eq (P : USize) : ∀ (m : Nat) (n : USize), n.toNat = m →
    ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float),
      Gen26.fixUntilR P n tree hP node hn other v = Gen16.fixUntilGo P n tree hP node hn other v := by
  intro m
  induction m with
  | zero =>
    intro n hm tree hP node hn other v
    have hz : n = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [Gen26.fixUntilR, dite_eq_left hz, Gen16.fixUntilGo, dite_eq_left hz]
  | succ m ih =>
    intro n hm tree hP node hn other v
    have hz : n ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [Gen26.fixUntilR, dite_eq_right hz, Gen16.fixUntilGo, dite_eq_right hz]
    simp only [ih (n - 1) (by rw [Gen16.pred_toNat n hz]; omega)]

theorem fixPathR26_eq (P : USize) : ∀ (m : Nat) (n : USize), n.toNat = m →
    ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (v : Float),
      Gen26.fixPathR P n tree hP node hn v = Gen16.fixPathGo P n tree hP node hn v := by
  intro m
  induction m with
  | zero =>
    intro n hm tree hP node hn v
    have hz : n = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [Gen26.fixPathR, dite_eq_left hz, Gen16.fixPathGo, dite_eq_left hz]
  | succ m ih =>
    intro n hm tree hP node hn v
    have hz : n ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [Gen26.fixPathR, dite_eq_right hz, Gen16.fixPathGo, dite_eq_right hz]
    simp only [ih (n - 1) (by rw [Gen16.pred_toNat n hz]; omega)]

theorem setBoundsR26_eq (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (nW : USize)
    (hi : FloatArray) (hhi : nW.toNat ≤ hi.size) (h0 h1 g0 g1 : Float) (ds : Array Gen18.DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat) :
    ∀ m (i : USize), ds.size - i.toNat = m → ∀ (tree : FloatArray)
      (htree : 2 * P.toNat ≤ tree.size) (pending : USize) hpend,
      Gen26.setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend =
        Gen21.setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend := by
  intro m
  induction m with
  | zero =>
    intro i hm tree htree pending hpend
    have hge : ¬ i < ds.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize ds i h; omega
    rw [Gen26.setBoundsR, dite_eq_right hge, Gen21.setBoundsR, dite_eq_right hge]
    simp only [fixPathR26_eq P _ D rfl]
  | succ m ih =>
    intro i hm tree htree pending hpend
    by_cases h : i < ds.usize
    · have hs := Gen15.succ_toNat_of_lt_usize ds i h
      rw [Gen26.setBoundsR, dite_eq_left h, Gen21.setBoundsR, dite_eq_left h]
      simp only [ih (i + 1) (by omega), fixUntilR26_eq P _ D rfl]
    · rw [Gen26.setBoundsR, dite_eq_right h, Gen21.setBoundsR, dite_eq_right h]
      simp only [fixPathR26_eq P _ D rfl]

theorem rebracketR26_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (c : Gen19.CacheV) (hc : Gen20.Sized nW P c)
    (s : USize) (hs : s.toNat < nW.toNat) :
    Gen26.rebracketR W P hP2 D nW numRx rates hB pop hpop c hc s hs =
      Gen19.rebracketV W P P hP2 D pop c s := by
  rw [← rebracketR_eq W P hP2 D nW numRx rates hB pop hpop c hc s hs]
  simp only [Gen26.rebracketR, Gen21.rebracketR]
  rw [setBoundsR26_eq _ _ _ _ _ _ _ _ _ _ _ _ _ 0 rfl]

theorem refresh1_26_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (s : USize) (hs : s.toNat < nW.toNat)
    (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) :
    Gen26.refresh1 W P hP2 D nW numRx rates hB pop hpop s hs c hc =
      if Gen18.staleW (Gen18.cget W.ms s) (Gen18.cget pop s) (Gen18.cget c.lo s)
          (Gen18.cget c.hi s) then Gen19.rebracketV W P P hP2 D pop c s else c := by
  have hms := hB.ms
  have h1 := hc.1
  have h2 := hc.2.1
  simp only [Gen26.refresh1]
  rw [cget_uget W.ms _ (by omega), cget_uget pop _ (by omega), cget_uget c.lo _ (by omega),
    cget_uget c.hi _ (by omega), rebracketR26_eq]

/-! ## Records of one, two or three changes -/

/-- What the record of reaction `j` says about the reaction's changes array. -/
structure ChsAtV (chs : Array Gen18.ChangeW) (r : Gen26.RxV) : Prop where
  size : chs.size = if r.one then 1 else if r.three then 3 else 2
  onethree : r.one = true → r.three = false
  ch0 : ∀ h : 0 < chs.size, chs[0]'h = ⟨r.c0, r.add0, r.a0⟩
  ch1 : r.one = false → ∀ h : 1 < chs.size, chs[1]'h = ⟨r.c1, r.add1, r.a1⟩
  ch2 : r.three = true → ∀ h : 2 < chs.size, chs[2]'h = ⟨r.c2, r.add2, r.a2⟩

/-- A record of two or three changes as generation 21's. -/
def toW (r : Gen26.RxV) : Gen21.RxW :=
  ⟨r.s, r.t, r.c0, r.c1, r.c2, r.rate, r.a0, r.a1, r.a2, r.kind, r.three, r.add0, r.add1, r.add2⟩

theorem ChsAtV.chsAt {chs : Array Gen18.ChangeW} {r : Gen26.RxV} (h : ChsAtV chs r)
    (h1 : r.one = false) : ChsAt chs (toW r) :=
  ⟨by rw [h.size, ite_eq_right (by simp [h1])]; rfl, h.ch0, h.ch1 h1, h.ch2⟩

theorem RxAtV.chsAtV {W : Gen18.Compiled} {rates : FloatArray} {j : Nat} {r : Gen26.RxV}
    (hr : Gen26.RxAtV W rates j r) (hc : j < W.changes.size) : ChsAtV (W.changes[j]) r := by
  have e : W.changes[j]! = W.changes[j] := getElem!_pos W.changes j hc
  have hsz := hr.size
  rw [e] at hsz
  refine ⟨hsz, hr.onethree, fun h => ?_, fun h1 h => ?_, fun h3 h => ?_⟩
  · have e0 := hr.ch0
    rw [e, getElem!_pos _ 0 h] at e0
    exact e0
  · have e1 := hr.ch1 h1
    rw [e, getElem!_pos _ 1 h] at e1
    exact e1
  · have e2 := hr.ch2 h3
    rw [e, getElem!_pos _ 2 h] at e2
    exact e2

theorem rxV_at {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen26.RxV}
    (hR : Gen26.RxOKV W rates m rxs) (j : USize) (h : j.toNat < rxs.size) :
    Gen26.RxAtV W rates j.toNat (rxs.uget j h) :=
  hR.get j.toNat h (hR.size ▸ h)

theorem rxV_rate {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen26.RxV}
    (hR : Gen26.RxOKV W rates m rxs) (j : USize) (h : j.toNat < rxs.size) :
    (rxs.uget j h).rate = Gen17.fget rates j := by
  rw [(rxV_at hR j h).rate, fget_eq]

theorem rxV_eval {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen26.RxV}
    (hR : Gen26.RxOKV W rates m rxs) (j : USize) (h : j.toNat < rxs.size) (pop : FloatArray)
    (hs : (rxs.uget j h).s.toNat < pop.size) (ht : (rxs.uget j h).t.toNat < pop.size) :
    Gen26.evalV (rxs.uget j h) pop hs ht = Gen18.evalW (Gen17.aget W.factors j) pop := by
  have hr := rxV_at hR j h
  simp only [Gen26.evalV, Gen18.evalW, aget_eq, ← hr.kind, ← hr.s, ← hr.t,
    cget_uget pop _ hs, cget_uget pop _ ht]

theorem apply1C_eq (s : USize) (add : Bool) (amount : Float) (ms : FloatArray) (c : Gen19.CacheV)
    (nW : USize) (hs : s.toNat < nW.toNat) (hms : nW.toNat ≤ ms.size)
    (hlo : nW.toNat ≤ c.lo.size) (hhi : nW.toNat ≤ c.hi.size) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (stale : Bool) :
    Gen25.apply1C s add amount ms c nW hs hms hlo hhi pop hpop stale =
      Gen21.apply1 s add amount ms c.lo c.hi nW hs hms hlo hhi pop hpop stale := rfl

theorem small_chs {chs : Array Gen18.ChangeW} (h : chs.size ≤ 3) : chs.size < USize.size := by
  have hU : 4 ≤ USize.size := by
    have hsz' : USize.size = 2 ^ System.Platform.numBits := rfl
    rcases System.Platform.numBits_eq with h | h <;> rw [hsz', h] <;> decide
  omega

/-- The changes of a record of reaction `j` are the changes array's, applied in order. -/
theorem applyRV_eq (chs : Array Gen18.ChangeW) (r : Gen26.RxV) (hch : ChsAtV chs r) (nW : USize)
    (h0 : r.c0.toNat < nW.toNat) (h1 : r.one = false → r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (ms : FloatArray) (c : Gen19.CacheV)
    (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ c.lo.size) (hhi : nW.toNat ≤ c.hi.size)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (hpopU : pop.size < USize.size) :
    Gen26.applyRV r nW h0 h1 h2 ms c hms hlo hhi pop hpop =
      Gen18.applyW chs ms c.lo c.hi nW 0 pop false := by
  by_cases h1' : r.one = true
  · have hsz : chs.size = 1 := by rw [hch.size, ite_eq_left h1']
    have hu := usize_toNat_of_small chs (small_chs (by omega))
    have i0 : (0 : USize) < chs.usize := by
      show (0 : USize).toNat < chs.usize.toNat; rw [hu, USize.toNat_zero]; omega
    have t1 : ((0 : USize) + 1).toNat = 1 := Gen15.succ_toNat_of_lt_usize chs 0 i0
    have i1 : ¬ (0 : USize) + 1 < chs.usize := by
      show ¬ ((0 : USize) + 1).toNat < chs.usize.toNat; rw [t1, hu]; omega
    have e0 : chs[(0 : USize).toNat]'(Gen15.lt_size_of_lt_usize chs 0 i0) =
        ⟨r.c0, r.add0, r.a0⟩ := hch.ch0 _
    have hp1 := stepPop_size ⟨r.c0, r.add0, r.a0⟩ pop
    rw [applyW_step chs ms c.lo c.hi nW 0 pop false i0 _ e0,
      applyW_end chs ms c.lo c.hi nW _ _ _ i1]
    unfold Gen26.applyRV
    rw [apply1C_eq, apply1_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hpopU]
    dsimp only
    rw [dite_eq_left h1', cset_uset _ _ _ (by rw [hp1]; omega) (by rw [hp1]; exact hpopU)]
  · have h1f : r.one = false := by simpa using h1'
    have hc1 := h1 h1f
    have hsz := hch.size
    rw [ite_eq_right (by simp [h1f])] at hsz
    have hu := usize_toNat_of_small chs (small_chs (by rw [hsz]; split <;> omega))
    have hs2 : 2 ≤ chs.size := by rw [hsz]; split <;> omega
    have i0 : (0 : USize) < chs.usize := by
      show (0 : USize).toNat < chs.usize.toNat; rw [hu, USize.toNat_zero]; omega
    have t1 : ((0 : USize) + 1).toNat = 1 := Gen15.succ_toNat_of_lt_usize chs 0 i0
    have i1 : (0 : USize) + 1 < chs.usize := by
      show ((0 : USize) + 1).toNat < chs.usize.toNat; rw [t1, hu]; omega
    have t2 : ((0 : USize) + 1 + 1).toNat = 2 := by
      rw [Gen15.succ_toNat_of_lt_usize chs _ i1, t1]
    have e0 : chs[(0 : USize).toNat]'(Gen15.lt_size_of_lt_usize chs 0 i0) =
        ⟨r.c0, r.add0, r.a0⟩ := hch.ch0 _
    have e1 : chs[((0 : USize) + 1).toNat]'(Gen15.lt_size_of_lt_usize chs _ i1) =
        ⟨r.c1, r.add1, r.a1⟩ := by
      have := hch.ch1 h1f (by omega)
      simp only [t1]
      exact this
    have hp1 := stepPop_size ⟨r.c0, r.add0, r.a0⟩ pop
    have hp2 := stepPop_size ⟨r.c1, r.add1, r.a1⟩ (stepPop ⟨r.c0, r.add0, r.a0⟩ pop)
    unfold Gen26.applyRV
    rw [apply1C_eq, apply1_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hpopU]
    dsimp only
    rw [dite_eq_right h1', apply1C_eq, apply1_eq _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    dsimp only
    rw [applyW_step chs ms c.lo c.hi nW 0 pop false i0 _ e0,
      applyW_step chs ms c.lo c.hi nW _ _ _ i1 _ e1]
    split
    · rename_i h3
      have hs3 : chs.size = 3 := by rw [hsz, ite_eq_left h3]
      have i2 : (0 : USize) + 1 + 1 < chs.usize := by
        show ((0 : USize) + 1 + 1).toNat < chs.usize.toNat; rw [t2, hu]; omega
      have t3 : ((0 : USize) + 1 + 1 + 1).toNat = 3 := by
        rw [Gen15.succ_toNat_of_lt_usize chs _ i2, t2]
      have e2 : chs[((0 : USize) + 1 + 1).toNat]'(Gen15.lt_size_of_lt_usize chs _ i2) =
          ⟨r.c2, r.add2, r.a2⟩ := by
        have := hch.ch2 h3 (by omega)
        simp only [t2]
        exact this
      rw [apply1C_eq, apply1_eq _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
      dsimp only
      have i3 : ¬ (0 : USize) + 1 + 1 + 1 < chs.usize := by
        show ¬ ((0 : USize) + 1 + 1 + 1).toNat < chs.usize.toNat; rw [t3, hu]; omega
      rw [applyW_step chs ms c.lo c.hi nW _ _ _ i2 _ e2, applyW_end chs ms c.lo c.hi nW _ _ _ i3,
        cset_uset _ _ _ (by rw [stepPop_size, hp2, hp1]; omega)
          (by rw [stepPop_size, hp2, hp1]; exact hpopU)]
    · rename_i h3
      have hs3 : chs.size = 2 := by rw [hsz, ite_eq_right h3]
      have i2 : ¬ (0 : USize) + 1 + 1 < chs.usize := by
        show ¬ ((0 : USize) + 1 + 1).toNat < chs.usize.toNat; rw [t2, hu]; omega
      rw [applyW_end chs ms c.lo c.hi nW _ _ _ i2,
        cset_uset _ _ _ (by rw [hp2, hp1]; omega) (by rw [hp2, hp1]; exact hpopU)]

theorem smallV_eq (chs : Array Gen18.ChangeW) (r : Gen26.RxV) (hch : ChsAtV chs r)
    (pop : FloatArray) (h0 : r.c0.toNat < pop.size) (h1 : r.one = false → r.c1.toNat < pop.size)
    (h2 : r.three = true → r.c2.toNat < pop.size) :
    Gen26.smallV r pop h0 h1 h2 = Gen18.smallFrom chs pop 0 := by
  by_cases h1' : r.one = true
  · have hsz : chs.size = 1 := by rw [hch.size, ite_eq_left h1']
    have hu := usize_toNat_of_small chs (small_chs (by omega))
    have i0 : (0 : USize) < chs.usize := by
      show (0 : USize).toNat < chs.usize.toNat; rw [hu, USize.toNat_zero]; omega
    have t1 : ((0 : USize) + 1).toNat = 1 := Gen15.succ_toNat_of_lt_usize chs 0 i0
    have i1 : ¬ (0 : USize) + 1 < chs.usize := by
      show ¬ ((0 : USize) + 1).toNat < chs.usize.toNat; rw [t1, hu]; omega
    have e0 : chs[(0 : USize).toNat]'(Gen15.lt_size_of_lt_usize chs 0 i0) =
        ⟨r.c0, r.add0, r.a0⟩ := hch.ch0 _
    rw [smallFrom_step chs pop 0 i0 _ e0, smallFrom_end chs pop _ i1]
    simp only [Gen26.smallV, cget_uget pop _ h0, h1', dite_true]
  · have h1f : r.one = false := by simpa using h1'
    have hsz := hch.size
    rw [ite_eq_right (by simp [h1f])] at hsz
    have hu := usize_toNat_of_small chs (small_chs (by rw [hsz]; split <;> omega))
    have hs2 : 2 ≤ chs.size := by rw [hsz]; split <;> omega
    have i0 : (0 : USize) < chs.usize := by
      show (0 : USize).toNat < chs.usize.toNat; rw [hu, USize.toNat_zero]; omega
    have t1 : ((0 : USize) + 1).toNat = 1 := Gen15.succ_toNat_of_lt_usize chs 0 i0
    have i1 : (0 : USize) + 1 < chs.usize := by
      show ((0 : USize) + 1).toNat < chs.usize.toNat; rw [t1, hu]; omega
    have t2 : ((0 : USize) + 1 + 1).toNat = 2 := by
      rw [Gen15.succ_toNat_of_lt_usize chs _ i1, t1]
    have e0 : chs[(0 : USize).toNat]'(Gen15.lt_size_of_lt_usize chs 0 i0) =
        ⟨r.c0, r.add0, r.a0⟩ := hch.ch0 _
    have e1 : chs[((0 : USize) + 1).toNat]'(Gen15.lt_size_of_lt_usize chs _ i1) =
        ⟨r.c1, r.add1, r.a1⟩ := by
      have := hch.ch1 h1f (by omega)
      simp only [t1]
      exact this
    rw [smallFrom_step chs pop 0 i0 _ e0, smallFrom_step chs pop _ i1 _ e1]
    simp only [Gen26.smallV, cget_uget pop _ h0, cget_uget pop _ (h1 h1f), h1f,
      Bool.false_eq_true, dite_false]
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
      rw [smallFrom_step chs pop _ i2 _ e2, smallFrom_end chs pop _ i3]
      simp only [h3, dite_true, cget_uget pop _ (h2 h3)]
    · have h3' : r.three = false := by simpa using h3
      have hs3 : chs.size = 2 := by rw [hsz, ite_eq_right (by simp [h3'])]
      have i2 : ¬ (0 : USize) + 1 + 1 < chs.usize := by
        show ¬ ((0 : USize) + 1 + 1).toNat < chs.usize.toNat; rw [t2, hu]; omega
      rw [smallFrom_end chs pop _ i2]
      simp only [h3', Bool.false_eq_true, dite_false]

theorem refreshFromRV_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (chs : Array Gen18.ChangeW) (r : Gen26.RxV) (hch : ChsAtV chs r)
    (h0 : r.c0.toNat < nW.toNat) (h1 : r.one = false → r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) :
    Gen26.refreshFromRV W P hP2 D nW numRx rates hB r h0 h1 h2 pop hpop c hc =
      Gen19.refreshFromV W P P hP2 D chs pop 0 c := by
  by_cases h1' : r.one = true
  · have hsz : chs.size = 1 := by rw [hch.size, ite_eq_left h1']
    have hu := usize_toNat_of_small chs (small_chs (by omega))
    have i0 : (0 : USize) < chs.usize := by
      show (0 : USize).toNat < chs.usize.toNat; rw [hu, USize.toNat_zero]; omega
    have t1 : ((0 : USize) + 1).toNat = 1 := Gen15.succ_toNat_of_lt_usize chs 0 i0
    have i1 : ¬ (0 : USize) + 1 < chs.usize := by
      show ¬ ((0 : USize) + 1).toNat < chs.usize.toNat; rw [t1, hu]; omega
    have e0 : chs[(0 : USize).toNat]'(Gen15.lt_size_of_lt_usize chs 0 i0) =
        ⟨r.c0, r.add0, r.a0⟩ := hch.ch0 _
    rw [refreshFromV_step W P P hP2 D chs pop 0 c i0 _ e0, refreshFromV_end W P P hP2 D chs pop _ _ i1]
    simp only [Gen26.refreshFromRV, refresh1_26_eq, h1', dite_true]
  · have h1f : r.one = false := by simpa using h1'
    have hsz := hch.size
    rw [ite_eq_right (by simp [h1f])] at hsz
    have hu := usize_toNat_of_small chs (small_chs (by rw [hsz]; split <;> omega))
    have hs2 : 2 ≤ chs.size := by rw [hsz]; split <;> omega
    have i0 : (0 : USize) < chs.usize := by
      show (0 : USize).toNat < chs.usize.toNat; rw [hu, USize.toNat_zero]; omega
    have t1 : ((0 : USize) + 1).toNat = 1 := Gen15.succ_toNat_of_lt_usize chs 0 i0
    have i1 : (0 : USize) + 1 < chs.usize := by
      show ((0 : USize) + 1).toNat < chs.usize.toNat; rw [t1, hu]; omega
    have t2 : ((0 : USize) + 1 + 1).toNat = 2 := by
      rw [Gen15.succ_toNat_of_lt_usize chs _ i1, t1]
    have e0 : chs[(0 : USize).toNat]'(Gen15.lt_size_of_lt_usize chs 0 i0) =
        ⟨r.c0, r.add0, r.a0⟩ := hch.ch0 _
    have e1 : chs[((0 : USize) + 1).toNat]'(Gen15.lt_size_of_lt_usize chs _ i1) =
        ⟨r.c1, r.add1, r.a1⟩ := by
      have := hch.ch1 h1f (by omega)
      simp only [t1]
      exact this
    rw [refreshFromV_step W P P hP2 D chs pop 0 c i0 _ e0,
      refreshFromV_step W P P hP2 D chs pop _ _ i1 _ e1]
    simp only [Gen26.refreshFromRV, refresh1_26_eq, h1f, Bool.false_eq_true, dite_false]
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
      rw [refreshFromV_step W P P hP2 D chs pop _ _ i2 _ e2,
        refreshFromV_end W P P hP2 D chs pop _ _ i3]
      simp only [h3, dite_true]
    · have h3' : r.three = false := by simpa using h3
      have hs3 : chs.size = 2 := by rw [hsz, ite_eq_right (by simp [h3'])]
      have i2 : ¬ (0 : USize) + 1 + 1 < chs.usize := by
        show ¬ ((0 : USize) + 1 + 1).toNat < chs.usize.toNat; rw [t2, hu]; omega
      rw [refreshFromV_end W P P hP2 D chs pop _ _ i2]
      simp only [h3', Bool.false_eq_true, dite_false]

theorem rxV_chs {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen26.RxV}
    (hR : Gen26.RxOKV W rates m rxs) (hm : m ≤ W.changes.size) (j : USize)
    (h : j.toNat < rxs.size) :
    Gen17.aget W.changes j = W.changes[j.toNat]'(by have := hR.size; omega) ∧
      ChsAtV (W.changes[j.toNat]'(by have := hR.size; omega)) (rxs.uget j h) := by
  have hc : j.toNat < W.changes.size := by have := hR.size; omega
  exact ⟨by rw [aget_eq, getElem!_pos W.changes j.toNat hc], RxAtV.chsAtV (rxV_at hR j h) hc⟩

theorem rxV_apply {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen26.RxV}
    (hR : Gen26.RxOKV W rates m rxs) (hm : m ≤ W.changes.size) (j : USize)
    (h : j.toNat < rxs.size) (nW : USize) (h0 : (rxs.uget j h).c0.toNat < nW.toNat)
    (h1 : (rxs.uget j h).one = false → (rxs.uget j h).c1.toNat < nW.toNat)
    (h2 : (rxs.uget j h).three = true → (rxs.uget j h).c2.toNat < nW.toNat)
    (ms : FloatArray) (c : Gen19.CacheV) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ c.lo.size)
    (hhi : nW.toNat ≤ c.hi.size) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (hpopU : pop.size < USize.size) :
    Gen26.applyRV (rxs.uget j h) nW h0 h1 h2 ms c hms hlo hhi pop hpop =
      Gen18.applyW (Gen17.aget W.changes j) ms c.lo c.hi nW 0 pop false := by
  obtain ⟨e, hch⟩ := rxV_chs hR hm j h
  rw [e]
  exact applyRV_eq _ _ hch nW h0 h1 h2 ms c hms hlo hhi pop hpop hpopU

theorem rxV_small {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen26.RxV}
    (hR : Gen26.RxOKV W rates m rxs) (hm : m ≤ W.changes.size) (j : USize)
    (h : j.toNat < rxs.size) (pop : FloatArray) (h0 : (rxs.uget j h).c0.toNat < pop.size)
    (h1 : (rxs.uget j h).one = false → (rxs.uget j h).c1.toNat < pop.size)
    (h2 : (rxs.uget j h).three = true → (rxs.uget j h).c2.toNat < pop.size) :
    Gen26.smallV (rxs.uget j h) pop h0 h1 h2 = Gen18.smallFrom (Gen17.aget W.changes j) pop 0 := by
  obtain ⟨e, hch⟩ := rxV_chs hR hm j h
  rw [e]
  exact smallV_eq _ _ hch pop h0 h1 h2

theorem rxV_refresh {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen26.RxV}
    (hR : Gen26.RxOKV W rates m rxs) (hm : m ≤ W.changes.size) (j : USize)
    (h : j.toNat < rxs.size) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (hB : Gen20.Bounds W nW P numRx rates)
    (h0 : (rxs.uget j h).c0.toNat < nW.toNat)
    (h1 : (rxs.uget j h).one = false → (rxs.uget j h).c1.toNat < nW.toNat)
    (h2 : (rxs.uget j h).three = true → (rxs.uget j h).c2.toNat < nW.toNat) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) :
    Gen26.refreshFromRV W P hP2 D nW numRx rates hB (rxs.uget j h) h0 h1 h2 pop hpop c hc =
      Gen19.refreshFromV W P P hP2 D (Gen17.aget W.changes j) pop 0 c := by
  obtain ⟨e, hch⟩ := rxV_chs hR hm j h
  rw [e]
  exact refreshFromRV_eq W P hP2 D nW numRx rates hB _ _ hch h0 h1 h2 pop hpop c hc

/-! ## The driver -/

theorem run26_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (hL : Gen22.Level P D 1) (rxs : Array Gen26.RxV)
    (hR : Gen26.RxOKV W rates numRx.toNat rxs) (horizon : Float) (save : Bool) (cap : USize)
    (fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = f →
      Gen26.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
      evW.toNat = fuel → prW.toNat = prFuel →
      Gen26.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have h0 : prW = 0 := USize.toNat_inj.mp (by rw [hpr]; rfl)
    rw [Gen26.run, dite_eq_left h0, Gen19.run, dite_eq_left h0]
  | succ pf ih =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have hT := tree_usize P hP2 c.tree hc.2.2
    have hU := hB.nU
    have hm := hB.changes
    have hpopU : pop.size < USize.size := by omega
    have ih' : ∀ pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
        Gen26.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
            (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
          Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW (prW - 1)
            pop c now total elapsed s0 s1 s2 s3 count trace :=
      fun pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
        ih evW (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
          (usize_pred_toNat hpr)
    by_cases he : evW = 0
    · rw [Gen26.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_left he, descendG26_eq, rxV_rate hR, rxV_eval hR, Gen25.stateOfV]
      simp only [uget_fget, ih', dite_eq_ite, ite_false_not]
    · have hev0 : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
      obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hn' : ∀ (prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
          Gen26.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
              (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
            Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap (evW - 1)
              prW pop c now total elapsed s0 s1 s2 s3 count trace :=
        fun prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
          hnext f hf (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace
            (by rw [Gen16.pred_toNat evW he]; omega)
      rw [Gen26.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_right he, descendG26_eq, rxV_rate hR, rxV_eval hR,
        rxV_apply hR hm (hpopU := hpopU), rxV_small hR hm, rxV_refresh hR hm,
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

/-- Generation 26's driver returns what generation 19's returns. -/
theorem gen26_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (hL : Gen22.Level P D 1) (rxs : Array Gen26.RxV)
    (hR : Gen26.RxOKV W rates numRx.toNat rxs) (horizon : Float) (save : Bool) (cap : USize) :
    ∀ fuel prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize)
      trace, evW.toNat = fuel → prW.toNat = prFuel →
      Gen26.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run26_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    refine run26_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
      (f + 1) ?_
    intro f' hf' evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
    obtain rfl : f' = f := by omega
    exact ih prW.toNat evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev rfl

/-- Generation 26 starts as generation 25 does. Where they differ, on a network with a reaction
of one change, generation 25 falls through generation 21's start to generation 20's, whose
driver agrees with generation 19's as generation 26's does. -/
theorem start26_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (count : Nat) (trace : Array (Float × State)) :
    Gen26.start C codes horizon save cap fuel pop c now rng count trace =
      Gen25.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen26.start Gen25.start
  dsimp only
  split
  · rename_i h
    split
    · exact (gen26_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).trans (gen25_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).symm
    · rename_i h25
      unfold Gen21.start
      dsimp only
      split
      · split
        · rename_i h21a h21b
          exact (h25 ⟨h21a, h21b.1, h21b.2.1, h21b.2.2.1, h21b.2.2.2.1, h21b.2.2.2.2.1,
            h21b.2.2.2.2.2.1, h21b.2.2.2.2.2.2, h.2.2.2.2.2.2.2.2⟩).elim
        · unfold Gen20.start
          dsimp only
          split
          · split
            · exact (gen26_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).trans (gen20_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).symm
            · rename_i hs20
              exact (hs20 ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
                h.2.2.2.2.2.2.1⟩).elim
          · rename_i h20
            exact (h20 h.1).elim
      · rename_i h21
        exact (h21 h.1).elim
  · rename_i h
    split
    · rename_i h25
      refine (h ⟨h25.1, h25.2.1, h25.2.2.1, h25.2.2.2.1, h25.2.2.2.2.1, h25.2.2.2.2.2.1,
        h25.2.2.2.2.2.2.1, ?_, h25.2.2.2.2.2.2.2.2⟩).elim
      have hc := h25.2.2.2.2.2.2.2.1
      rw [Array.all_eq_true] at hc ⊢
      intro i hi
      have := hc i hi
      simp only [Bool.or_eq_true, beq_iff_eq] at this ⊢
      rcases this with h2 | h3
      · exact Or.inl (Or.inr h2)
      · exact Or.inr h3
    · rfl

/-- Generation 26 returns what generation 25 returns, on every network and input. -/
theorem gen26_eq_gen25 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen26.simulate net initial start horizon rng maxEvents save cap =
      Gen25.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen26.simulate Gen25.simulate
  simp only [start26_eq]

/-- **Generation 26 is the specification.** For every network whose reactant species are in
range and every input, generation 26 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen26_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen26.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen26_eq_gen25, gen25_simulate_eq net hwf]

end JumpProcessesLean.Proofs
