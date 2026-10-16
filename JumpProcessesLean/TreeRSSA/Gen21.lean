import JumpProcessesLean.TreeRSSA.Gen20

/-!
# Tree-RSSA, generation 21: one record per reaction

Generation 20 reads a proposed reaction's rate from `rates` and its factor through the pointer
`W.factors[j]`, and a firing reaction reaches each of its changes through `W.changes[j]`, an array
of pointers to change records. On the large networks these records do not fit in the caches and
the chain of dependent loads stalls the driver. Generation 21 builds one record per reaction at
the start (`RxW`): the rate, the factor and the two or three changes as scalar fields, read with
one load. Firing, the count test and the refreshes take the record's changes in order
(`applyR`, `smallR`, `refreshFromR`), as generation 20's loops take the changes array. The start
requires every reaction to change two or three species; otherwise generation 20 runs.
-/

namespace JumpProcessesLean.TreeRSSA.Gen21

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)
open Gen18 (ChangeW Compiled compileW staleW ff2 ofCounts toCounts allSmall twoPow25)
open Gen19 (CacheV toCache rateMax)
open Gen18 (DepW bracketLo bracketHi)
open Gen20 (Bounds boundsOK boundsOK_spec Sized size_uset one_toNat)

/-- Generation 11's word descent, compiled in this module so that the driver inlines it. -/
def descendW (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) : USize :=
  if hk : k < P then
    have hk' : k.toNat < P.toNat := hk
    have h2 : (2 * k).toNat < tree.size := by rw [Gen11.usize_two_mul k (by omega)]; omega
    let left := tree.uget (2 * k) h2
    if x < left then
      descendW tree P hP hP2 (2 * k) (by rw [Gen11.usize_two_mul k (by omega)]; omega) x
    else
      descendW tree P hP hP2 (2 * k + 1) (by rw [Gen11.usize_two_mul_add_one k (by omega)]; omega)
        (x - left)
  else k
termination_by P.toNat - k.toNat
decreasing_by
  · have := (show k.toNat < P.toNat from hk)
    rw [Gen11.usize_two_mul k (by omega)]; omega
  · have := (show k.toNat < P.toNat from hk)
    rw [Gen11.usize_two_mul_add_one k (by omega)]; omega

/-- The descent ends below `2P`. -/
theorem descendW_lt (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      k.toNat < 2 * P.toNat → (descendW tree P hP hP2 k hk0 x).toNat < 2 * P.toNat := by
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm hk2
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
    exact hk2
  | succ m ih =>
    intro k hk0 x hm hk2
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega) (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega) (by rw [h21]; omega)
    · rw [descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
      exact hk2

/-! ## Records -/

/-- A reaction's rate, its factor (`kind`, `s`, `t` as in `FactorW`) and its changes
`(c0, add0, a0)`, `(c1, add1, a1)` and, if `three`, `(c2, add2, a2)`. -/
structure RxW where
  s : USize
  t : USize
  c0 : USize
  c1 : USize
  c2 : USize
  rate : Float
  a0 : Float
  a1 : Float
  a2 : Float
  kind : UInt64
  three : Bool
  add0 : Bool
  add1 : Bool
  add2 : Bool
  deriving Inhabited

/-- The change that pads a record of two changes. -/
def noChange : ChangeW := ⟨0, true, 0⟩

/-- Reaction `j`'s record. -/
def rxOf (W : Compiled) (rates : FloatArray) (j : Nat) : RxW :=
  let f := W.factors[j]!
  let chs := W.changes[j]!
  let ch0 := chs.getD 0 noChange
  let ch1 := chs.getD 1 noChange
  let ch2 := chs.getD 2 noChange
  { s := f.s, t := f.t, c0 := ch0.species, c1 := ch1.species, c2 := ch2.species,
    rate := rates.get! j, a0 := ch0.amount, a1 := ch1.amount, a2 := ch2.amount, kind := f.kind,
    three := chs.size == 3, add0 := ch0.add, add1 := ch1.add, add2 := ch2.add }

/-- The records of reactions `0, …, m - 1`. -/
def buildRx (W : Compiled) (rates : FloatArray) (m : Nat) : Array RxW :=
  (Array.range m).map (rxOf W rates)

/-- Record `r` holds reaction `j`: its rate, its factor and its two or three changes. -/
structure RxAt (W : Compiled) (rates : FloatArray) (j : Nat) (r : RxW) : Prop where
  rate : r.rate = rates.get! j
  kind : r.kind = (W.factors[j]!).kind
  s : r.s = (W.factors[j]!).s
  t : r.t = (W.factors[j]!).t
  size : (W.changes[j]!).size = if r.three then 3 else 2
  ch0 : (W.changes[j]!)[0]! = ⟨r.c0, r.add0, r.a0⟩
  ch1 : (W.changes[j]!)[1]! = ⟨r.c1, r.add1, r.a1⟩
  ch2 : r.three = true → (W.changes[j]!)[2]! = ⟨r.c2, r.add2, r.a2⟩

/-- The records hold reactions `0, …, m - 1`. -/
structure RxOK (W : Compiled) (rates : FloatArray) (m : Nat) (rxs : Array RxW) : Prop where
  size : rxs.size = m
  get : ∀ j (h : j < rxs.size), j < m → RxAt W rates j rxs[j]

theorem rxOf_at (W : Compiled) (rates : FloatArray) (j : Nat) (hj : j < W.changes.size)
    (h23 : (W.changes[j]).size = 2 ∨ (W.changes[j]).size = 3) :
    RxAt W rates j (rxOf W rates j) := by
  have e : W.changes[j]! = W.changes[j] := getElem!_pos W.changes j hj
  have hs : 2 ≤ (W.changes[j]).size := by omega
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [rxOf, e]
    rcases h23 with h | h <;> simp [h]
  · simp only [rxOf, e, Array.getD, dite_eq_left (show 0 < (W.changes[j]).size by omega)]
    exact getElem!_pos _ 0 (by omega)
  · simp only [rxOf, e, Array.getD, dite_eq_left (show 1 < (W.changes[j]).size by omega)]
    exact getElem!_pos _ 1 (by omega)
  · intro h3
    have h3' : (W.changes[j]).size = 3 := by
      simp only [rxOf, e, beq_iff_eq] at h3; exact h3
    simp only [rxOf, e, Array.getD, dite_eq_left (show 2 < (W.changes[j]).size by omega)]
    exact getElem!_pos _ 2 (by omega)

theorem buildRx_ok (W : Compiled) (rates : FloatArray) (m : Nat) (hm : m ≤ W.changes.size)
    (h23 : W.changes.all (fun chs => chs.size == 2 || chs.size == 3) = true) :
    RxOK W rates m (buildRx W rates m) := by
  refine ⟨by simp [buildRx], fun j h hj => ?_⟩
  have hc : j < W.changes.size := by omega
  have e : (buildRx W rates m)[j] = rxOf W rates j := by simp [buildRx]
  rw [e]
  refine rxOf_at W rates j hc ?_
  rw [Array.all_eq_true] at h23
  have := h23 j hc
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  exact this

/-- The factor's species of a record are in range. -/
theorem RxAt.factorBounds {W : Compiled} {rates : FloatArray} {j : Nat} {r : RxW}
    {nW P numRx : USize} (hB : Bounds W nW P numRx rates) (hj : j < numRx.toNat)
    (h : RxAt W rates j r) : r.s.toNat < nW.toNat ∧ r.t.toNat < nW.toNat := by
  have hf : j < W.factors.size := by have := hB.factors; omega
  rw [h.s, h.t, getElem!_pos W.factors j hf]
  exact hB.factorST j hf

/-- The changed species of a record are in range. -/
theorem RxAt.changeBounds {W : Compiled} {rates : FloatArray} {j : Nat} {r : RxW}
    {nW P numRx : USize} (hB : Bounds W nW P numRx rates) (hj : j < numRx.toNat)
    (h : RxAt W rates j r) :
    r.c0.toNat < nW.toNat ∧ r.c1.toNat < nW.toNat ∧ (r.three = true → r.c2.toNat < nW.toNat) := by
  have hc : j < W.changes.size := by have := hB.changes; omega
  have e : W.changes[j]! = W.changes[j] := getElem!_pos W.changes j hc
  have hsz := h.size
  rw [e] at hsz
  have hs2 : 2 ≤ (W.changes[j]).size := by rw [hsz]; cases r.three <;> simp
  refine ⟨?_, ?_, fun h3 => ?_⟩
  · have e0 := h.ch0
    rw [e, getElem!_pos _ 0 (by omega)] at e0
    have := hB.changeS j hc 0 (by omega)
    rw [e0] at this
    exact this
  · have e1 := h.ch1
    rw [e, getElem!_pos _ 1 (by omega)] at e1
    have := hB.changeS j hc 1 (by omega)
    rw [e1] at this
    exact this
  · have hs3 : 3 ≤ (W.changes[j]).size := by rw [hsz, ite_eq_left h3]; exact Nat.le_refl 3
    have e2 := h.ch2 h3
    rw [e, getElem!_pos _ 2 (by omega)] at e2
    have := hB.changeS j hc 2 (by omega)
    rw [e2] at this
    exact this

/-- The factor of a record at the counts. -/
@[inline] def evalR (r : RxW) (pop : FloatArray) (hs : r.s.toNat < pop.size)
    (ht : r.t.toNat < pop.size) : Float :=
  let x := pop.uget r.s hs
  if r.kind = 0 then x else if r.kind = 1 then ff2 x else x * pop.uget r.t ht

/-! ## Firing -/

/-- One change `(s, add, amount)` applied to the counts, and the flag of a species that left its
bracket: one step of generation 20's `applyU`. -/
@[inline] def apply1 (s : USize) (add : Bool) (amount : Float) (ms lo hi : FloatArray)
    (nW : USize) (hs : s.toNat < nW.toNat) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) (pop : FloatArray) (hpop : nW.toNat < pop.size) (stale : Bool) :
    {p : FloatArray // p.size = pop.size} × Bool :=
  let old := pop.uget s (by omega)
  if add then
    let v := old + amount
    (⟨pop.uset s v (by omega), size_uset _ _ _ _⟩, stale || decide (hi.uget s (by omega) < v))
  else
    let v := if old ≤ amount then floatZero else old - amount
    (⟨pop.uset s v (by omega), size_uset _ _ _ _⟩,
      stale || decide (v < lo.uget s (by omega)) ||
        (decide (v < ms.uget s (by omega)) && hi.uget s (by omega) != v))

/-- Generation 20's `applyU` on a record's changes: apply them and write to entry `nW` whether a
changed species left its bracket. -/
def applyR (r : RxW) (nW : USize) (h0 : r.c0.toNat < nW.toNat) (h1 : r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (ms lo hi : FloatArray)
    (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size) (hhi : nW.toNat ≤ hi.size)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) : FloatArray :=
  let (⟨p0, e0⟩, st0) := apply1 r.c0 r.add0 r.a0 ms lo hi nW h0 hms hlo hhi pop hpop false
  let (⟨p1, e1⟩, st1) :=
    apply1 r.c1 r.add1 r.a1 ms lo hi nW h1 hms hlo hhi p0 (by omega) st0
  if h : r.three = true then
    let (⟨p2, e2⟩, st2) :=
      apply1 r.c2 r.add2 r.a2 ms lo hi nW (h2 h) hms hlo hhi p1 (by omega) st1
    p2.uset nW (if st2 then floatOne else floatZero) (by omega)
  else p1.uset nW (if st1 then floatOne else floatZero) (by omega)

theorem applyR_size (r : RxW) (nW : USize) (h0 : r.c0.toNat < nW.toNat)
    (h1 : r.c1.toNat < nW.toNat) (h2 : r.three = true → r.c2.toNat < nW.toNat)
    (ms lo hi : FloatArray) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) (pop : FloatArray) (hpop : nW.toNat < pop.size) :
    (applyR r nW h0 h1 h2 ms lo hi hms hlo hhi pop hpop).size = pop.size := by
  simp only [applyR]
  split
  · rw [size_uset]
    exact (apply1 _ _ _ _ _ _ _ _ _ _ _ _ _ _).1.property.trans
      ((apply1 _ _ _ _ _ _ _ _ _ _ _ _ _ _).1.property.trans
        (apply1 _ _ _ _ _ _ _ _ _ _ _ _ _ _).1.property)
  · rw [size_uset]
    exact (apply1 _ _ _ _ _ _ _ _ _ _ _ _ _ _).1.property.trans
      (apply1 _ _ _ _ _ _ _ _ _ _ _ _ _ _).1.property

/-- Generation 20's `smallU` on a record's changes: every changed species' count is below
`2^25`. -/
@[inline] def smallR (r : RxW) (pop : FloatArray) (h0 : r.c0.toNat < pop.size)
    (h1 : r.c1.toNat < pop.size) (h2 : r.three = true → r.c2.toNat < pop.size) : Bool :=
  if pop.uget r.c0 h0 < twoPow25 then
    if pop.uget r.c1 h1 < twoPow25 then
      if h : r.three = true then
        if pop.uget r.c2 (h2 h) < twoPow25 then true else false
      else true
    else false
  else false

/-! ## Refreshes -/

/-- Generation 20's `setBoundsU`, compiled in this module so that the refreshes inline it. -/
def setBoundsR (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (nW : USize)
    (hi : FloatArray) (hhi : nW.toNat ≤ hi.size) (h0 h1 g0 g1 : Float) (ds : Array DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat)
    (i : USize) (tree : FloatArray) (htree : 2 * P.toNat ≤ tree.size) (pending : USize)
    (hpend : pending = 0 ∨ pending.toNat < 2 * P.toNat) : FloatArray :=
  if h : i < ds.usize then
    have hi' := Gen15.lt_size_of_lt_usize ds i h
    let d := ds.uget i hi'
    have hd : d.k.toNat < P.toNat ∧ d.partner.toNat ≤ nW.toNat := hds i.toNat hi'
    let pH := if hp : d.partner = 0 then floatOne
      else hi.uget (d.partner - 1) (by
        have : d.partner.toNat ≠ 0 := fun h0 => hp (USize.toNat_inj.mp (by rw [h0]; rfl))
        rw [Gen20.usize_sub_one_toNat hp]; omega)
    let bN := if d.two then h1 else h0
    if bN == (if d.two then g1 else g0) then
      setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds (i + 1) tree htree pending hpend
    else if pH == floatZero then
      setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds (i + 1) tree htree pending hpend
    else
      let leaf := P + d.k
      have hleaf : leaf.toNat = P.toNat + d.k.toNat := by
        have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hpend' : pending ≠ 0 → pending.toNat < 2 * P.toNat := fun hz => hpend.resolve_left hz
      let tree' := if hz : pending = 0 then tree
        else Gen16.fixUntilGo P D tree htree pending (hpend' hz) leaf
          (tree.uget pending (by have := hpend' hz; omega))
      have htree' : 2 * P.toNat ≤ tree'.size := by
        simp only [tree']
        split
        · exact htree
        · rw [Gen20.fixUntilGo_size P _ D rfl]; exact htree
      setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds (i + 1)
        (tree'.uset leaf (d.rate * (bN * pH)) (by omega)) (by rw [size_uset]; exact htree') leaf
        (Or.inr (by omega))
  else if hz : pending = 0 then tree
    else Gen16.fixPathGo P D tree htree pending (hpend.resolve_left hz)
      (tree.uget pending (by have := hpend.resolve_left hz; omega))
termination_by ds.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize ds i h]; omega)

theorem setBoundsR_size (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (nW : USize)
    (hi : FloatArray) (hhi : nW.toNat ≤ hi.size) (h0 h1 g0 g1 : Float) (ds : Array DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat) :
    ∀ m (i : USize), ds.size - i.toNat = m → ∀ (tree : FloatArray)
      (htree : 2 * P.toNat ≤ tree.size) (pending : USize) hpend,
      (setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend).size =
        tree.size := by
  intro m
  induction m with
  | zero =>
    intro i hm tree htree pending hpend
    have hge : ¬ i < ds.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize ds i h; omega
    rw [setBoundsR, dite_eq_right hge]
    split
    · rfl
    · rw [Gen20.fixPathGo_size P _ D rfl]
  | succ m ih =>
    intro i hm tree htree pending hpend
    by_cases h : i < ds.usize
    · have hs := Gen15.succ_toNat_of_lt_usize ds i h
      rw [setBoundsR, dite_eq_left h]
      dsimp only
      repeat' split
      all_goals first
        | exact ih (i + 1) (by omega) _ _ _ _
        | (rw [ih (i + 1) (by omega), size_uset, Gen20.fixUntilGo_size P _ D rfl])
        | (rw [ih (i + 1) (by omega), size_uset])
    · rw [setBoundsR, dite_eq_right h]
      split
      · rfl
      · rw [Gen20.fixPathGo_size P _ D rfl]

/-- Generation 20's `rebracketU` through this module's `setBoundsR`. -/
@[inline] def rebracketR (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (c : CacheV) (hc : Sized nW P c) (s : USize)
    (hs : s.toNat < nW.toNat) : CacheV :=
  have hms := hB.ms
  have hdeps := hB.deps
  let x := (pop.uget s (by omega)).toUInt64
  let m := (W.ms.uget s (by omega)).toUInt64
  let hiS := c.hi.uget s (by have := hc.2.1; omega)
  let loN := (bracketLo m x).toFloat
  let hiN := (bracketHi m x).toFloat
  let lo := c.lo.uset s loN (by have := hc.1; omega)
  let hi := c.hi.uset s hiN (by have := hc.2.1; omega)
  ⟨lo, hi, setBoundsR P hP2 D nW hi (by rw [size_uset]; exact Nat.le_of_eq hc.2.1.symm) hiN (ff2 hiN) hiS (ff2 hiS)
    (W.deps.uget s (by omega)) (fun k h => hB.depKP s.toNat (by omega) k h) 0 c.tree
    (Nat.le_of_eq hc.2.2.symm) 0 (Or.inl rfl)⟩

theorem rebracketR_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (c : CacheV) (hc : Sized nW P c) (s : USize)
    (hs : s.toNat < nW.toNat) :
    Sized nW P (rebracketR W P hP2 D nW numRx rates hB pop hpop c hc s hs) := by
  refine ⟨?_, ?_, ?_⟩
  · show (c.lo.uset _ _ _).size = nW.toNat
    rw [size_uset]; exact hc.1
  · show (c.hi.uset _ _ _).size = nW.toNat
    rw [size_uset]; exact hc.2.1
  · show (setBoundsR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).size = 2 * P.toNat
    rw [setBoundsR_size _ _ _ _ _ _ _ _ _ _ _ _ _ 0 rfl]
    exact hc.2.2


/-- Rebracket species `s` if it left its bracket: one step of generation 20's
`refreshFromU`. -/
@[inline] def refresh1 (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (s : USize) (hs : s.toNat < nW.toNat) (c : CacheV)
    (hc : Sized nW P c) : CacheV :=
  have hms := hB.ms
  if staleW (W.ms.uget s (by omega)) (pop.uget s (by omega))
      (c.lo.uget s (by have := hc.1; omega)) (c.hi.uget s (by have := hc.2.1; omega)) then
    rebracketR W P hP2 D nW numRx rates hB pop hpop c hc s hs
  else c

theorem refresh1_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (s : USize) (hs : s.toNat < nW.toNat) (c : CacheV)
    (hc : Sized nW P c) :
    Sized nW P (refresh1 W P hP2 D nW numRx rates hB pop hpop s hs c hc) := by
  simp only [refresh1]
  split
  · exact rebracketR_sized W P hP2 D nW numRx rates hB pop hpop c hc s hs
  · exact hc

/-- Generation 20's `refreshFromU` on a record's changes. -/
def refreshFromR (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (r : RxW)
    (h0 : r.c0.toNat < nW.toNat) (h1 : r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (c : CacheV) (hc : Sized nW P c) : CacheV :=
  let c0 := refresh1 W P hP2 D nW numRx rates hB pop hpop r.c0 h0 c hc
  have e0 := refresh1_sized W P hP2 D nW numRx rates hB pop hpop r.c0 h0 c hc
  let c1 := refresh1 W P hP2 D nW numRx rates hB pop hpop r.c1 h1 c0 e0
  have e1 := refresh1_sized W P hP2 D nW numRx rates hB pop hpop r.c1 h1 c0 e0
  if h : r.three = true then refresh1 W P hP2 D nW numRx rates hB pop hpop r.c2 (h2 h) c1 e1
  else c1

theorem refreshFromR_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates)
    (r : RxW) (h0 : r.c0.toNat < nW.toNat) (h1 : r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (c : CacheV) (hc : Sized nW P c) :
    Sized nW P (refreshFromR W P hP2 D nW numRx rates hB r h0 h1 h2 pop hpop c hc) := by
  simp only [refreshFromR]
  split
  · exact refresh1_sized _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact refresh1_sized _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## The driver -/

/-- Generation 20's driver reading each proposed reaction's record. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Compiled) (msN : Array Nat) (n : Nat)
    (hms : msN.size = n) (hval : Gen15.ValidChanges C n) (nW : USize) (numRx : USize) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Bounds W nW P numRx rates) (rxs : Array RxW) (hR : RxOK W rates numRx.toNat rxs)
    (horizon : Float) (save : Bool) (cap : USize)
    (evFuel prFuel : USize) (pop : FloatArray) (hpop : pop.size = nW.toNat + 1) (c : CacheV)
    (hc : Sized nW P c) (now total elapsed : Float) (s0 s1 s2 s3 : UInt64) (count : USize)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  if _hz : prFuel = 0 then .error .proposalLimit
  else
    have hP1 := hB.leaves
    have htree : 2 * P.toNat ≤ c.tree.size := Nat.le_of_eq hc.2.2.symm
    let rng : Xoshiro := ⟨s0, s1, s2, s3⟩
    let (u, rng) := rng.uniform
    if !decide (floatZero ≤ u) then .error .invalidUniform
    else if !decide (u < floatOne) then .error .invalidUniform
    else
      let (e, rng) := rng.exponential
      if !decide (e < floatInf) then .error .invalidExponential
      else if !decide (floatZero < e) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !decide (elapsed < floatInf) then .error .invalidTime
        else if !decide (floatNegInf < elapsed) then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !decide (floatZero ≤ v) then .error .invalidUniform
          else if !decide (v < floatOne) then .error .invalidUniform
          else
            let k := descendW c.tree P htree hP2 1 Gen11.usize_one_pos (u * total)
            have hk : k.toNat < 2 * P.toNat := descendW_lt c.tree P htree hP2 _ 1
              Gen11.usize_one_pos (u * total) (Nat.le_refl _)
              (by rw [one_toNat]; omega)
            let j := k - P
            if hacc : (if hj : j < numRx then
                have hjn : j.toNat < numRx.toNat := hj
                have hjr : j.toNat < rxs.size := by have := hR.size; omega
                let r := rxs.uget j hjr
                have hst : r.s.toNat < nW.toNat ∧ r.t.toNat < nW.toNat :=
                  (hR.get j.toNat hjr hjn).factorBounds hB hjn
                let threshold := v * c.tree.uget k (by omega)
                let actual := r.rate * evalR r pop (by omega) (by omega)
                decide (floatZero < actual) && decide (threshold ≤ actual)
              else false) = true then
              have hj : j < numRx := by
                by_cases hn : j < numRx
                · exact hn
                · rw [dite_eq_right hn] at hacc; exact absurd hacc Bool.false_ne_true
              let time := now + elapsed / total
              if !decide (time < floatInf) then .error .invalidTime
              else if !decide (floatNegInf < time) then .error .invalidTime
              else if !decide (now ≤ time) then .error .invalidTime
              else if !decide (time ≤ horizon) then
                let st : State := ⟨ofCounts pop n, ofCounts c.lo n, ofCounts c.hi n⟩
                .ok ⟨st, horizon, count.toNat, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                  trace.push (horizon, st)⟩
              else if he : evFuel = 0 then .error .eventLimit
              else
                have hjn : j.toNat < numRx.toNat := hj
                have hjr : j.toNat < rxs.size := by have := hR.size; omega
                let r := rxs.uget j hjr
                have hcb : r.c0.toNat < nW.toNat ∧ r.c1.toNat < nW.toNat ∧
                    (r.three = true → r.c2.toNat < nW.toNat) :=
                  (hR.get j.toNat hjr hjn).changeBounds hB hjn
                let p := applyR r nW hcb.1 hcb.2.1 hcb.2.2 W.ms c.lo c.hi hB.ms
                  (Nat.le_of_eq hc.1.symm) (Nat.le_of_eq hc.2.1.symm) pop (by omega)
                have hp : p.size = nW.toNat + 1 := by rw [applyR_size]; exact hpop
                if p.uget nW (by omega) == floatZero then
                  let trace := if save then trace.push (time, ⟨ofCounts p n, ofCounts c.lo n,
                    ofCounts c.hi n⟩) else trace
                  run C codes W msN n hms hval nW numRx P hP2 D rates hB rxs hR horizon save cap
                    (evFuel - 1) cap p hp c hc time total floatZero rng.s0 rng.s1 rng.s2 rng.s3
                    (count + 1) trace
                else if smallR r p (by omega) (by omega)
                    (fun h => by have := hcb.2.2 h; omega) then
                  let c' := refreshFromR W P hP2 D nW numRx rates hB r hcb.1 hcb.2.1
                    hcb.2.2 p (by omega) c hc
                  have hc' : Sized nW P c' := refreshFromR_sized W P hP2 D nW numRx rates hB r
                    hcb.1 hcb.2.1 hcb.2.2 p (by omega) c hc
                  let trace := if save then trace.push (time, ⟨ofCounts p n, ofCounts c'.lo n,
                    ofCounts c'.hi n⟩) else trace
                  let total := c'.tree.uget 1 (by
                    have := hc'.2.2
                    rw [one_toNat]
                    omega)
                  if !decide (total < floatInf) then .error (.invalidRate numRx.toNat)
                  else if !decide (floatNegInf < total) then .error (.invalidRate numRx.toNat)
                  else if !decide (floatZero < total) then
                    let st : State := ⟨ofCounts p n, ofCounts c'.lo n, ofCounts c'.hi n⟩
                    .ok ⟨st, horizon, count.toNat + 1, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                      trace.push (horizon, st)⟩
                  else
                    run C codes W msN n hms hval nW numRx P hP2 D rates hB rxs hR horizon save
                      cap (evFuel - 1) cap p hp c' hc' time total floatZero rng.s0 rng.s1 rng.s2
                      rng.s3 (count + 1) trace
                else
                  -- a count reached `2^25`: generation 17's refresh, then generation 17
                  let popN := ofCounts p n
                  if hpN : popN.size = n then
                    let cN := toCache C n c
                    let chsN := C.changes[j.toNat]!
                    let c' := chsN.foldl
                      (fun c ch => Gen16.refresh C.gen5 codes P hP2 msN popN c ch.species) cN
                    let trace := if save then trace.push (time, ⟨popN, c'.lo, c'.hi⟩) else trace
                    let total := Gen17.fget c'.tree 1
                    if !decide (total < floatInf) then .error (.invalidRate numRx.toNat)
                    else if !decide (floatNegInf < total) then .error (.invalidRate numRx.toNat)
                    else if !decide (floatZero < total) then
                      .ok ⟨⟨popN, c'.lo, c'.hi⟩, horizon, count.toNat + 1,
                        ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩, trace.push (horizon, ⟨popN, c'.lo, c'.hi⟩)⟩
                    else if hs : c'.lo.size = n ∧ c'.hi.size = n then
                      Gen17.run C codes msN n hms hval numRx P hP2 C.gen5.base.rates
                        C.gen5.base.factors horizon save cap (evFuel - 1) cap popN hpN c' hs.1 hs.2
                        time total floatZero rng.s0 rng.s1 rng.s2 rng.s3 (count + 1) trace
                    else .error .invalidShape
                  else .error .invalidShape
            else
              run C codes W msN n hms hval nW numRx P hP2 D rates hB rxs hR horizon save cap
                evFuel (prFuel - 1) pop hpop c hc now total elapsed rng.s0 rng.s1 rng.s2 rng.s3
                count trace
termination_by (evFuel.toNat, prFuel.toNat)
decreasing_by
  all_goals first
    | (have : evFuel.toNat ≠ 0 := fun h => he (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat evFuel he]; exact Prod.Lex.left _ _ (by omega))
    | (have : prFuel.toNat ≠ 0 := fun h => _hz (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat prFuel _hz]; exact Prod.Lex.right _ (by omega))

/-- Generation 20's start, entering generation 21's driver when also every reaction changes two
or three species. -/
@[inline] def start (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let n := C.gen5.base.ms.size
  let total := c.tree.get! 1
  let W := compileW C codes
  let popW := (toCounts pop).push 0
  let cV : CacheV := ⟨toCounts c.lo, toCounts c.hi, c.tree⟩
  if h : Gen7.finite total = true ∧ decide (floatZero < total) = true ∧
      2 * C.gen5.base.leaves < USize.size then
    if hs : (pop.size = n ∧ c.lo.size = n ∧ c.hi.size = n ∧ Gen15.validChanges C n = true ∧
        Gen17.changesOK C = true ∧ Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
        count + fuel < USize.size ∧ cap < USize.size ∧ C.gen5.base.numRx < USize.size ∧
        n + 1 < USize.size ∧ allSmall pop = true ∧ allSmall c.lo = true ∧ allSmall c.hi = true ∧
        allSmall C.gen5.base.ms = true ∧
        C.gen5.base.factors.all (Gen18.FactorW.ok n) = true ∧
        codes.all (·.all fun c => c == 0 || c == 1 || (c % 4 == 0 && decide (4 ≤ c) &&
          decide (c / 4 ≤ n))) = true ∧
        codes.size = n ∧ C.gen5.depRates.size = n ∧ C.gen5.base.deps.size = n ∧
        (List.range n).all (fun s => (codes[s]!).size == (C.gen5.base.deps[s]!).size &&
          (C.gen5.depRates[s]!).size == (C.gen5.base.deps[s]!).size &&
          decide ((C.gen5.base.deps[s]!).size < USize.size) &&
          (C.gen5.base.deps[s]!).all (· < C.gen5.base.leaves)) = true ∧
        C.changes.all (·.all fun ch => decide (ch.up < 67108864) && decide (ch.down < 67108864))
          = true ∧
        C.gen5.base.rates.data.all (fun r => decide (floatZero ≤ r) && decide (r < rateMax))
          = true) ∧
        boundsOK W n.toUSize C.gen5.base.leaves.toUSize C.gen5.base.numRx.toUSize
          C.gen5.base.rates = true ∧
        popW.size = n.toUSize.toNat + 1 ∧ cV.lo.size = n.toUSize.toNat ∧
        cV.hi.size = n.toUSize.toNat ∧ cV.tree.size = 2 * C.gen5.base.leaves.toUSize.toNat ∧
        W.changes.all (fun chs => chs.size == 2 || chs.size == 3) = true then
      have hB := boundsOK_spec hs.2.1
      have hnum : C.gen5.base.numRx.toUSize.toNat = C.gen5.base.numRx := by
        rw [Nat.toUSize, USize.toNat_ofNat_of_lt' hs.1.2.2.2.2.2.2.2.2.1]
      run C codes W C.gen5.base.ms n rfl (Gen15.validChanges_spec hs.1.2.2.2.1) n.toUSize
        C.gen5.base.numRx.toUSize C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h.2.2)
        C.gen5.base.depth.toUSize C.gen5.base.rates hB
        (buildRx W C.gen5.base.rates C.gen5.base.numRx)
        (by
          rw [hnum]
          exact buildRx_ok W C.gen5.base.rates C.gen5.base.numRx
            (by have := hB.changes; omega) hs.2.2.2.2.2.2)
        horizon save cap.toUSize fuel.toUSize cap.toUSize popW hs.2.2.1 cV
        ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩
        now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize trace
    else Gen20.start C codes horizon save cap fuel pop c now rng count trace
  else Gen20.start C codes horizon save cap fuel pop c now rng count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(Gen7.finite start && Gen7.finite horizon && decide (start ≤ horizon)) then
    .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen6.compile net
    Gen21.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen21
