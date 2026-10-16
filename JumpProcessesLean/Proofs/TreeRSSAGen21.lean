import JumpProcessesLean.Proofs.TreeRSSAGen20
import JumpProcessesLean.TreeRSSA.Gen21

/-!
# Generation 21 is generation 19, hence the specification

A record holds its reaction's rate, factor and changes (`RxAt`), so reading the proposed
reaction's record reads what generation 19's tested accesses read (`rx_rate`, `rx_eval`), and
the steps over the record's two or three changes are generation 19's loops over the changes
array, unrolled (`rx_apply`, `rx_small`, `rx_refresh`). The drivers then agree as generation 20's
does (`gen21_run_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)
open JumpProcessesLean.TreeRSSA.Gen7 (floatInf floatNegInf)

theorem descendW21_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      Gen21.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x := by
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [Gen21.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
      Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
  | succ m ih =>
    intro k hk0 x hm
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [Gen21.descendW, dite_eq_left_of_eq_true (eq_true hkP),
        Gen19.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega)
    · rw [Gen21.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
        Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]

theorem descendW21_eq' (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) :
    Gen21.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x :=
  descendW21_eq tree P hP hP2 _ k hk0 x le_rfl

/-! ## Refreshes -/

theorem setBoundsR_eq (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (nW : USize)
    (hi : FloatArray) (hhi : nW.toNat ≤ hi.size) (h0 h1 g0 g1 : Float) (ds : Array Gen18.DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat) :
    ∀ m (i : USize), ds.size - i.toNat = m → ∀ (tree : FloatArray)
      (htree : 2 * P.toNat ≤ tree.size) (pending : USize) hpend,
      Gen21.setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend =
        Gen20.setBoundsU P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend := by
  intro m
  induction m with
  | zero =>
    intro i hm tree htree pending hpend
    have hge : ¬ i < ds.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize ds i h; omega
    rw [Gen21.setBoundsR, dite_eq_right hge, Gen20.setBoundsU, dite_eq_right hge]
  | succ m ih =>
    intro i hm tree htree pending hpend
    by_cases h : i < ds.usize
    · have hs := Gen15.succ_toNat_of_lt_usize ds i h
      rw [Gen21.setBoundsR, dite_eq_left h, Gen20.setBoundsU, dite_eq_left h]
      simp only [ih (i + 1) (by omega)]
    · rw [Gen21.setBoundsR, dite_eq_right h, Gen20.setBoundsU, dite_eq_right h]

theorem rebracketR_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (c : Gen19.CacheV) (hc : Gen20.Sized nW P c)
    (s : USize) (hs : s.toNat < nW.toNat) :
    Gen21.rebracketR W P hP2 D nW numRx rates hB pop hpop c hc s hs =
      Gen19.rebracketV W P P hP2 D pop c s := by
  rw [← rebracketU_eq W P hP2 D nW numRx rates hB pop hpop c hc s hs]
  simp only [Gen21.rebracketR, Gen20.rebracketU]
  rw [setBoundsR_eq _ _ _ _ _ _ _ _ _ _ _ _ _ 0 rfl]

theorem refresh1_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (s : USize) (hs : s.toNat < nW.toNat)
    (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) :
    Gen21.refresh1 W P hP2 D nW numRx rates hB pop hpop s hs c hc =
      if Gen18.staleW (Gen18.cget W.ms s) (Gen18.cget pop s) (Gen18.cget c.lo s)
          (Gen18.cget c.hi s) then Gen19.rebracketV W P P hP2 D pop c s else c := by
  have hms := hB.ms
  have h1 := hc.1
  have h2 := hc.2.1
  simp only [Gen21.refresh1]
  rw [cget_uget W.ms _ (by omega), cget_uget pop _ (by omega), cget_uget c.lo _ (by omega),
    cget_uget c.hi _ (by omega), rebracketR_eq]

/-! ## Unrolled loops -/

/-- One change, as generation 18's `applyW` applies it. -/
def stepPop (ch : Gen18.ChangeW) (pop : FloatArray) : FloatArray :=
  let old := Gen18.cget pop ch.species
  Gen18.cset pop ch.species
    (if ch.add then old + ch.amount else if old ≤ ch.amount then floatZero else old - ch.amount)

/-- The stale flag after one change, as generation 18's `applyW` computes it. -/
def stepFlag (ch : Gen18.ChangeW) (ms lo hi pop : FloatArray) (stale : Bool) : Bool :=
  let s := ch.species
  let old := Gen18.cget pop s
  if ch.add then stale || decide (Gen18.cget hi s < old + ch.amount)
  else
    let v := if old ≤ ch.amount then floatZero else old - ch.amount
    stale || decide (v < Gen18.cget lo s) || (decide (v < Gen18.cget ms s) && Gen18.cget hi s != v)

theorem applyW_step (chs : Array Gen18.ChangeW) (ms lo hi : FloatArray) (n i : USize)
    (pop : FloatArray) (stale : Bool) (h : i < chs.usize) (ch : Gen18.ChangeW)
    (hch : chs[i.toNat]'(Gen15.lt_size_of_lt_usize chs i h) = ch) :
    Gen18.applyW chs ms lo hi n i pop stale =
      Gen18.applyW chs ms lo hi n (i + 1) (stepPop ch pop) (stepFlag ch ms lo hi pop stale) := by
  rw [Gen18.applyW, dite_eq_left h]
  simp only [Array.uget, hch, stepPop, stepFlag]
  cases ch.add <;> rfl

theorem applyW_end (chs : Array Gen18.ChangeW) (ms lo hi : FloatArray) (n i : USize)
    (pop : FloatArray) (stale : Bool) (h : ¬ i < chs.usize) :
    Gen18.applyW chs ms lo hi n i pop stale =
      Gen18.cset pop n (if stale then floatOne else floatZero) := by
  rw [Gen18.applyW, dite_eq_right h]

theorem smallFrom_step (chs : Array Gen18.ChangeW) (pop : FloatArray) (i : USize)
    (h : i < chs.usize) (ch : Gen18.ChangeW)
    (hch : chs[i.toNat]'(Gen15.lt_size_of_lt_usize chs i h) = ch) :
    Gen18.smallFrom chs pop i =
      if Gen18.cget pop ch.species < Gen18.twoPow25 then Gen18.smallFrom chs pop (i + 1)
      else false := by
  rw [Gen18.smallFrom, dite_eq_left h]
  simp only [Array.uget, hch]

theorem smallFrom_end (chs : Array Gen18.ChangeW) (pop : FloatArray) (i : USize)
    (h : ¬ i < chs.usize) : Gen18.smallFrom chs pop i = true := by
  rw [Gen18.smallFrom, dite_eq_right h]

theorem refreshFromV_step (W : Gen18.Compiled) (leaves P : USize)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (chs : Array Gen18.ChangeW) (pop : FloatArray)
    (i : USize) (c : Gen19.CacheV) (h : i < chs.usize) (ch : Gen18.ChangeW)
    (hch : chs[i.toNat]'(Gen15.lt_size_of_lt_usize chs i h) = ch) :
    Gen19.refreshFromV W leaves P hP2 D chs pop i c =
      Gen19.refreshFromV W leaves P hP2 D chs pop (i + 1)
        (if Gen18.staleW (Gen18.cget W.ms ch.species) (Gen18.cget pop ch.species)
            (Gen18.cget c.lo ch.species) (Gen18.cget c.hi ch.species) then
          Gen19.rebracketV W leaves P hP2 D pop c ch.species else c) := by
  rw [Gen19.refreshFromV, dite_eq_left h]
  simp only [Array.uget, hch]

theorem refreshFromV_end (W : Gen18.Compiled) (leaves P : USize)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (chs : Array Gen18.ChangeW) (pop : FloatArray)
    (i : USize) (c : Gen19.CacheV) (h : ¬ i < chs.usize) :
    Gen19.refreshFromV W leaves P hP2 D chs pop i c = c := by
  rw [Gen19.refreshFromV, dite_eq_right h]

theorem stepPop_size (ch : Gen18.ChangeW) (pop : FloatArray) :
    (stepPop ch pop).size = pop.size := fa_size_cset _ _ _

theorem apply1_val (s : USize) (add : Bool) (amount : Float) (ms lo hi : FloatArray)
    (nW : USize) (hs : s.toNat < nW.toNat) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (hpopU : pop.size < USize.size) (stale : Bool) :
    (Gen21.apply1 s add amount ms lo hi nW hs hms hlo hhi pop hpop stale).1.val =
      stepPop ⟨s, add, amount⟩ pop := by
  have h1 : s.toNat < pop.size := by omega
  simp only [stepPop]
  rw [cget_uget pop s h1, cset_uset pop s _ h1 hpopU]
  cases add <;> rfl

theorem apply1_flag (s : USize) (add : Bool) (amount : Float) (ms lo hi : FloatArray)
    (nW : USize) (hs : s.toNat < nW.toNat) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) (pop : FloatArray) (hpop : nW.toNat < pop.size) (stale : Bool) :
    (Gen21.apply1 s add amount ms lo hi nW hs hms hlo hhi pop hpop stale).2 =
      stepFlag ⟨s, add, amount⟩ ms lo hi pop stale := by
  simp only [stepFlag]
  rw [cget_uget pop s (by omega), cget_uget hi s (by omega), cget_uget lo s (by omega),
    cget_uget ms s (by omega)]
  cases add <;> rfl

/-- `apply1` is one step of generation 18's `applyW`. -/
theorem apply1_eq (s : USize) (add : Bool) (amount : Float) (ms lo hi : FloatArray)
    (nW : USize) (hs : s.toNat < nW.toNat) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (hpopU : pop.size < USize.size) (stale : Bool) :
    Gen21.apply1 s add amount ms lo hi nW hs hms hlo hhi pop hpop stale =
      (⟨stepPop ⟨s, add, amount⟩ pop, stepPop_size _ _⟩,
        stepFlag ⟨s, add, amount⟩ ms lo hi pop stale) :=
  Prod.ext (Subtype.ext (apply1_val s add amount ms lo hi nW hs hms hlo hhi pop hpop hpopU stale))
    (apply1_flag s add amount ms lo hi nW hs hms hlo hhi pop hpop stale)

/-! ## Records -/

theorem usize_toNat_of_small {α : Type} (a : Array α) (h : a.size < USize.size) :
    a.usize.toNat = a.size := by
  simp only [Array.usize, Nat.toUSize]
  exact USize.toNat_ofNat_of_lt' h

/-- What the record of reaction `j` says about the reaction's changes array. -/
structure ChsAt (chs : Array Gen18.ChangeW) (r : Gen21.RxW) : Prop where
  size : chs.size = if r.three then 3 else 2
  ch0 : ∀ h : 0 < chs.size, chs[0]'h = ⟨r.c0, r.add0, r.a0⟩
  ch1 : ∀ h : 1 < chs.size, chs[1]'h = ⟨r.c1, r.add1, r.a1⟩
  ch2 : r.three = true → ∀ h : 2 < chs.size, chs[2]'h = ⟨r.c2, r.add2, r.a2⟩

theorem RxAt.chsAt {W : Gen18.Compiled} {rates : FloatArray} {j : Nat} {r : Gen21.RxW}
    (hr : Gen21.RxAt W rates j r) (hc : j < W.changes.size) : ChsAt (W.changes[j]) r := by
  have e : W.changes[j]! = W.changes[j] := getElem!_pos W.changes j hc
  have hsz := hr.size
  rw [e] at hsz
  refine ⟨hsz, fun h => ?_, fun h => ?_, fun h3 h => ?_⟩
  · have e0 := hr.ch0
    rw [e, getElem!_pos _ 0 h] at e0
    exact e0
  · have e1 := hr.ch1
    rw [e, getElem!_pos _ 1 h] at e1
    exact e1
  · have e2 := hr.ch2 h3
    rw [e, getElem!_pos _ 2 h] at e2
    exact e2

theorem rx_at {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen21.RxW}
    (hR : Gen21.RxOK W rates m rxs) (j : USize) (h : j.toNat < rxs.size) :
    Gen21.RxAt W rates j.toNat (rxs.uget j h) :=
  hR.get j.toNat h (hR.size ▸ h)

theorem rx_rate {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen21.RxW}
    (hR : Gen21.RxOK W rates m rxs) (j : USize) (h : j.toNat < rxs.size) :
    (rxs.uget j h).rate = Gen17.fget rates j := by
  rw [(rx_at hR j h).rate, fget_eq]

theorem rx_eval {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen21.RxW}
    (hR : Gen21.RxOK W rates m rxs) (j : USize) (h : j.toNat < rxs.size) (pop : FloatArray)
    (hs : (rxs.uget j h).s.toNat < pop.size) (ht : (rxs.uget j h).t.toNat < pop.size) :
    Gen21.evalR (rxs.uget j h) pop hs ht = Gen18.evalW (Gen17.aget W.factors j) pop := by
  have hr := rx_at hR j h
  simp only [Gen21.evalR, Gen18.evalW, aget_eq, ← hr.kind, ← hr.s, ← hr.t,
    cget_uget pop _ hs, cget_uget pop _ ht]

/-- The changes of a record of reaction `j` are the changes array's, applied in order. -/
theorem applyR_eq (chs : Array Gen18.ChangeW) (r : Gen21.RxW) (hch : ChsAt chs r) (nW : USize)
    (h0 : r.c0.toNat < nW.toNat) (h1 : r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (ms lo hi : FloatArray)
    (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size) (hhi : nW.toNat ≤ hi.size)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (hpopU : pop.size < USize.size) :
    Gen21.applyR r nW h0 h1 h2 ms lo hi hms hlo hhi pop hpop =
      Gen18.applyW chs ms lo hi nW 0 pop false := by
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
  have hp1 := stepPop_size ⟨r.c0, r.add0, r.a0⟩ pop
  have hp2 := stepPop_size ⟨r.c1, r.add1, r.a1⟩ (stepPop ⟨r.c0, r.add0, r.a0⟩ pop)
  unfold Gen21.applyR
  rw [apply1_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hpopU]
  dsimp only
  rw [apply1_eq _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  dsimp only
  rw [applyW_step chs ms lo hi nW 0 pop false i0 _ e0,
    applyW_step chs ms lo hi nW _ _ _ i1 _ e1]
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
    rw [apply1_eq _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    dsimp only
    have i3 : ¬ (0 : USize) + 1 + 1 + 1 < chs.usize := by
      show ¬ ((0 : USize) + 1 + 1 + 1).toNat < chs.usize.toNat; rw [t3, hu]; omega
    rw [applyW_step chs ms lo hi nW _ _ _ i2 _ e2, applyW_end chs ms lo hi nW _ _ _ i3,
      cset_uset _ _ _ (by rw [stepPop_size, hp2, hp1]; omega) (by rw [stepPop_size, hp2, hp1]; exact hpopU)]
  · rename_i h3
    have hs3 : chs.size = 2 := by rw [hsz, ite_eq_right h3]
    have i2 : ¬ (0 : USize) + 1 + 1 < chs.usize := by
      show ¬ ((0 : USize) + 1 + 1).toNat < chs.usize.toNat; rw [t2, hu]; omega
    rw [applyW_end chs ms lo hi nW _ _ _ i2,
      cset_uset _ _ _ (by rw [hp2, hp1]; omega) (by rw [hp2, hp1]; exact hpopU)]

theorem smallR_eq (chs : Array Gen18.ChangeW) (r : Gen21.RxW) (hch : ChsAt chs r)
    (pop : FloatArray) (h0 : r.c0.toNat < pop.size) (h1 : r.c1.toNat < pop.size)
    (h2 : r.three = true → r.c2.toNat < pop.size) :
    Gen21.smallR r pop h0 h1 h2 = Gen18.smallFrom chs pop 0 := by
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
  rw [smallFrom_step chs pop 0 i0 _ e0, smallFrom_step chs pop _ i1 _ e1]
  simp only [Gen21.smallR, cget_uget pop _ h0, cget_uget pop _ h1]
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

theorem refreshFromR_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (chs : Array Gen18.ChangeW) (r : Gen21.RxW) (hch : ChsAt chs r)
    (h0 : r.c0.toNat < nW.toNat) (h1 : r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) :
    Gen21.refreshFromR W P hP2 D nW numRx rates hB r h0 h1 h2 pop hpop c hc =
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
  simp only [Gen21.refreshFromR, refresh1_eq]
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

theorem rx_chs {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen21.RxW}
    (hR : Gen21.RxOK W rates m rxs) (hm : m ≤ W.changes.size) (j : USize)
    (h : j.toNat < rxs.size) :
    Gen17.aget W.changes j = W.changes[j.toNat]'(by have := hR.size; omega) ∧
      ChsAt (W.changes[j.toNat]'(by have := hR.size; omega)) (rxs.uget j h) := by
  have hc : j.toNat < W.changes.size := by have := hR.size; omega
  exact ⟨by rw [aget_eq, getElem!_pos W.changes j.toNat hc], RxAt.chsAt (rx_at hR j h) hc⟩

theorem rx_apply {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen21.RxW}
    (hR : Gen21.RxOK W rates m rxs) (hm : m ≤ W.changes.size) (j : USize)
    (h : j.toNat < rxs.size) (nW : USize) (h0 : (rxs.uget j h).c0.toNat < nW.toNat)
    (h1 : (rxs.uget j h).c1.toNat < nW.toNat)
    (h2 : (rxs.uget j h).three = true → (rxs.uget j h).c2.toNat < nW.toNat)
    (ms lo hi : FloatArray) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (hpopU : pop.size < USize.size) :
    Gen21.applyR (rxs.uget j h) nW h0 h1 h2 ms lo hi hms hlo hhi pop hpop =
      Gen18.applyW (Gen17.aget W.changes j) ms lo hi nW 0 pop false := by
  obtain ⟨e, hch⟩ := rx_chs hR hm j h
  rw [e]
  exact applyR_eq _ _ hch nW h0 h1 h2 ms lo hi hms hlo hhi pop hpop hpopU

theorem rx_small {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen21.RxW}
    (hR : Gen21.RxOK W rates m rxs) (hm : m ≤ W.changes.size) (j : USize)
    (h : j.toNat < rxs.size) (pop : FloatArray) (h0 : (rxs.uget j h).c0.toNat < pop.size)
    (h1 : (rxs.uget j h).c1.toNat < pop.size)
    (h2 : (rxs.uget j h).three = true → (rxs.uget j h).c2.toNat < pop.size) :
    Gen21.smallR (rxs.uget j h) pop h0 h1 h2 = Gen18.smallFrom (Gen17.aget W.changes j) pop 0 := by
  obtain ⟨e, hch⟩ := rx_chs hR hm j h
  rw [e]
  exact smallR_eq _ _ hch pop h0 h1 h2

theorem rx_refresh {W : Gen18.Compiled} {rates : FloatArray} {m : Nat} {rxs : Array Gen21.RxW}
    (hR : Gen21.RxOK W rates m rxs) (hm : m ≤ W.changes.size) (j : USize)
    (h : j.toNat < rxs.size) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (hB : Gen20.Bounds W nW P numRx rates)
    (h0 : (rxs.uget j h).c0.toNat < nW.toNat) (h1 : (rxs.uget j h).c1.toNat < nW.toNat)
    (h2 : (rxs.uget j h).three = true → (rxs.uget j h).c2.toNat < nW.toNat) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) :
    Gen21.refreshFromR W P hP2 D nW numRx rates hB (rxs.uget j h) h0 h1 h2 pop hpop c hc =
      Gen19.refreshFromV W P P hP2 D (Gen17.aget W.changes j) pop 0 c := by
  obtain ⟨e, hch⟩ := rx_chs hR hm j h
  rw [e]
  exact refreshFromR_eq W P hP2 D nW numRx rates hB _ _ hch h0 h1 h2 pop hpop c hc

/-! ## The driver -/

theorem run21_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (rxs : Array Gen21.RxW)
    (hR : Gen21.RxOK W rates numRx.toNat rxs) (horizon : Float) (save : Bool) (cap : USize)
    (fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = f →
      Gen21.run C codes W msN n hms hval nW numRx P hP2 D rates hB rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
      evW.toNat = fuel → prW.toNat = prFuel →
      Gen21.run C codes W msN n hms hval nW numRx P hP2 D rates hB rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have h0 : prW = 0 := USize.toNat_inj.mp (by rw [hpr]; rfl)
    rw [Gen21.run, dite_eq_left h0, Gen19.run, dite_eq_left h0]
  | succ pf ih =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have hT := tree_usize P hP2 c.tree hc.2.2
    have hU := hB.nU
    have hm := hB.changes
    have hpopU : pop.size < USize.size := by omega
    have ih' : ∀ pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
        Gen21.run C codes W msN n hms hval nW numRx P hP2 D rates hB rxs hR horizon save cap evW
            (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
          Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW (prW - 1)
            pop c now total elapsed s0 s1 s2 s3 count trace :=
      fun pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
        ih evW (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
          (usize_pred_toNat hpr)
    by_cases he : evW = 0
    · rw [Gen21.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_left he, descendW21_eq', rx_rate hR, rx_eval hR]
      simp only [uget_fget, ih', dite_eq_ite, ite_false_not]
    · have hev0 : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
      obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hn' : ∀ (prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
          Gen21.run C codes W msN n hms hval nW numRx P hP2 D rates hB rxs hR horizon save cap
              (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
            Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap (evW - 1)
              prW pop c now total elapsed s0 s1 s2 s3 count trace :=
        fun prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
          hnext f hf (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace
            (by rw [Gen16.pred_toNat evW he]; omega)
      rw [Gen21.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_right he, descendW21_eq', rx_rate hR, rx_eval hR,
        rx_apply hR hm (hpopU := hpopU), rx_small hR hm, rx_refresh hR hm]
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

/-- Generation 21's driver returns what generation 19's returns. -/
theorem gen21_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (rxs : Array Gen21.RxW)
    (hR : Gen21.RxOK W rates numRx.toNat rxs) (horizon : Float) (save : Bool) (cap : USize) :
    ∀ fuel prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize)
      trace, evW.toNat = fuel → prW.toNat = prFuel →
      Gen21.run C codes W msN n hms hval nW numRx P hP2 D rates hB rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run21_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB rxs hR horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    refine run21_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB rxs hR horizon save cap
      (f + 1) ?_
    intro f' hf' evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
    obtain rfl : f' = f := by omega
    exact ih prW.toNat evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev rfl

theorem start21_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (count : Nat) (trace : Array (Float × State)) :
    Gen21.start C codes horizon save cap fuel pop c now rng count trace =
      Gen20.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen21.start
  dsimp only
  split
  · rename_i h
    split
    · rename_i hs
      unfold Gen20.start
      dsimp only
      split
      · split
        · exact (gen21_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).trans
            (gen20_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).symm
        · rename_i hs20
          exact (hs20 ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩).elim
      · rename_i h20
        exact (h20 h).elim
    · rfl
  · rfl

/-- Generation 21 returns what generation 20 returns, on every network and input. -/
theorem gen21_eq_gen20 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen21.simulate net initial start horizon rng maxEvents save cap =
      Gen20.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen21.simulate Gen20.simulate
  simp only [start21_eq]

/-- **Generation 21 is the specification.** For every network whose reactant species are in
range and every input, generation 21 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen21_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen21.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen21_eq_gen20, gen20_simulate_eq net hwf]

end JumpProcessesLean.Proofs
