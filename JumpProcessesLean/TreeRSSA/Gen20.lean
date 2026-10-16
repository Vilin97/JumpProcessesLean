import JumpProcessesLean.TreeRSSA.Gen19

/-!
# Tree-RSSA, generation 20: every access in bounds by proof

Generation 19 reads and writes its counts, brackets, records and tree through `cget`, `cset`,
`fget` and `aget`, which compare the index with the array's size on every access, and it tests
the tree's size once per proposal. The indices are always in range: changed and refreshed species
are below the species count, reactions below the reaction count, leaves below `2P`. Generation 20
carries these facts as proofs. The start tests the compiled records once (`boundsOK`); the
driver's arguments carry the sizes of the counts, the brackets and the tree, which firing and
refreshes keep; and every access is a `uget` or `uset` with its proof. The tree's path updates
call generation 16's walks directly.
-/

namespace JumpProcessesLean.TreeRSSA.Gen20

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)
open Gen18 (ChangeW DepW FactorW Compiled compileW staleW bracketLo bracketHi ff2 ofCounts
  toCounts allSmall twoPow25)
open Gen19 (CacheV lowerOf toCache rateMax)

theorem size_uset (a : FloatArray) (i : USize) (v : Float) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := Gen12.size_uset a i v h

theorem usize_sub_one_toNat {p : USize} (h : p ≠ 0) : (p - 1).toNat = p.toNat - 1 :=
  Gen16.pred_toNat p h

theorem one_toNat : (1 : USize).toNat = 1 := by
  rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]

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

/-! ## The compiled records' bounds -/

/-- Every index read from the compiled records is in range: species below `nW`, dependents'
leaves below `P`, and the records cover the reactions and the species. -/
structure Bounds (W : Compiled) (nW P numRx : USize) (rates : FloatArray) : Prop where
  nU : nW.toNat + 1 < USize.size
  leaves : 0 < P.toNat
  ms : nW.toNat ≤ W.ms.size
  rates : numRx.toNat ≤ rates.size
  factors : numRx.toNat ≤ W.factors.size
  factorST : ∀ j (h : j < W.factors.size),
    (W.factors[j]'h).s.toNat < nW.toNat ∧ (W.factors[j]'h).t.toNat < nW.toNat
  changes : numRx.toNat ≤ W.changes.size
  changeS : ∀ j (h : j < W.changes.size) k (hk : k < (W.changes[j]'h).size),
    ((W.changes[j]'h)[k]'hk).species.toNat < nW.toNat
  deps : nW.toNat ≤ W.deps.size
  depKP : ∀ s (h : s < W.deps.size) i (hi : i < (W.deps[s]'h).size),
    ((W.deps[s]'h)[i]'hi).k.toNat < P.toNat ∧ ((W.deps[s]'h)[i]'hi).partner.toNat ≤ nW.toNat

/-- `Bounds`, tested. -/
def boundsOK (W : Compiled) (nW P numRx : USize) (rates : FloatArray) : Bool :=
  decide (nW.toNat + 1 < USize.size) && decide (0 < P.toNat) && decide (nW.toNat ≤ W.ms.size) &&
    decide (numRx.toNat ≤ rates.size) &&
    decide (numRx.toNat ≤ W.factors.size) &&
    W.factors.all (fun f => decide (f.s.toNat < nW.toNat) && decide (f.t.toNat < nW.toNat)) &&
    decide (numRx.toNat ≤ W.changes.size) &&
    W.changes.all (·.all fun ch => decide (ch.species.toNat < nW.toNat)) &&
    decide (nW.toNat ≤ W.deps.size) &&
    W.deps.all (·.all fun d => decide (d.k.toNat < P.toNat) && decide (d.partner.toNat ≤ nW.toNat))

theorem boundsOK_spec {W : Compiled} {nW P numRx : USize} {rates : FloatArray}
    (h : boundsOK W nW P numRx rates = true) : Bounds W nW P numRx rates := by
  simp only [boundsOK, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hU, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨hU, h0, h1, h2, h3, fun j hj => ?_, h5, fun j hj k hk => ?_, h7, fun s hs i hi => ?_⟩
  · have := h4 j hj
    simpa using this
  · exact h6 j hj k hk
  · exact h8 s hs i hi

/-! ## Firing -/

/-- Generation 18's `applyW` with its accesses proved in bounds. -/
def applyU (chs : Array ChangeW) (nW : USize)
    (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat)
    (ms lo hi : FloatArray) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) (i : USize) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (stale : Bool) : FloatArray :=
  if h : i < chs.usize then
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    let ch := chs.uget i hi'
    let s := ch.species
    have hs : s.toNat < nW.toNat := hchs i.toNat hi'
    let old := pop.uget s (by omega)
    if ch.add then
      let v := old + ch.amount
      applyU chs nW hchs ms lo hi hms hlo hhi (i + 1) (pop.uset s v (by omega))
        (by rw [size_uset]; exact hpop) (stale || decide (hi.uget s (by omega) < v))
    else
      let v := if old ≤ ch.amount then floatZero else old - ch.amount
      applyU chs nW hchs ms lo hi hms hlo hhi (i + 1) (pop.uset s v (by omega))
        (by rw [size_uset]; exact hpop)
        (stale || decide (v < lo.uget s (by omega)) ||
          (decide (v < ms.uget s (by omega)) && hi.uget s (by omega) != v))
  else pop.uset nW (if stale then floatOne else floatZero) hpop
termination_by chs.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize chs i h]; omega)

theorem applyU_size (chs : Array ChangeW) (nW : USize)
    (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat)
    (ms lo hi : FloatArray) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ (pop : FloatArray) (hpop : nW.toNat < pop.size)
      (stale : Bool), (applyU chs nW hchs ms lo hi hms hlo hhi i pop hpop stale).size = pop.size := by
  intro m
  induction m with
  | zero =>
    intro i hm pop hpop stale
    have hge : ¬ i < chs.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize chs i h; omega
    rw [applyU, dite_eq_right hge, size_uset]
  | succ m ih =>
    intro i hm pop hpop stale
    by_cases h : i < chs.usize
    · have hs := Gen15.succ_toNat_of_lt_usize chs i h
      rw [applyU, dite_eq_left h]
      dsimp only
      split
      · rw [ih (i + 1) (by omega), size_uset]
      · rw [ih (i + 1) (by omega), size_uset]
    · rw [applyU, dite_eq_right h, size_uset]

/-- Generation 18's `smallFrom` with its accesses proved in bounds. -/
def smallU (chs : Array ChangeW) (nW : USize)
    (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (i : USize) : Bool :=
  if h : i < chs.usize then
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    let ch := chs.uget i hi'
    have hs : ch.species.toNat < nW.toNat := hchs i.toNat hi'
    if pop.uget ch.species (by omega) < twoPow25 then smallU chs nW hchs pop hpop (i + 1)
    else false
  else true
termination_by chs.size - i.toNat
decreasing_by rw [Gen15.succ_toNat_of_lt_usize chs i h]; omega

/-- Generation 18's `evalW` with its accesses proved in bounds. -/
@[inline] def evalU (f : FactorW) (pop : FloatArray) (hs : f.s.toNat < pop.size)
    (ht : f.t.toNat < pop.size) : Float :=
  let x := pop.uget f.s hs
  if f.kind = 0 then x else if f.kind = 1 then ff2 x else x * pop.uget f.t ht

/-! ## Refreshes -/

theorem fixUntilGo_size (P : USize) : ∀ (m : Nat) (n : USize), n.toNat = m →
    ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float),
      (Gen16.fixUntilGo P n tree hP node hn other v).size = tree.size := by
  intro m
  induction m with
  | zero =>
    intro n hm tree hP node hn other v
    have hz : n = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [Gen16.fixUntilGo, dite_eq_left hz]
  | succ m ih =>
    intro n hm tree hP node hn other v
    have hz : n ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [Gen16.fixUntilGo, dite_eq_right hz]
    dsimp only
    split
    · rfl
    · rw [ih _ (by rw [Gen16.pred_toNat n hz]; omega), Gen12.size_uset]

theorem fixPathGo_size (P : USize) : ∀ (m : Nat) (n : USize), n.toNat = m →
    ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (v : Float),
      (Gen16.fixPathGo P n tree hP node hn v).size = tree.size := by
  intro m
  induction m with
  | zero =>
    intro n hm tree hP node hn v
    have hz : n = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [Gen16.fixPathGo, dite_eq_left hz]
  | succ m ih =>
    intro n hm tree hP node hn v
    have hz : n ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [Gen16.fixPathGo, dite_eq_right hz]
    dsimp only
    rw [ih _ (by rw [Gen16.pred_toNat n hz]; omega), Gen12.size_uset]

/-- Generation 19's `setBoundsV` with its accesses proved in bounds and generation 16's walks
called directly. `pending` is the last changed leaf (`0` if none). -/
def setBoundsU (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (nW : USize)
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
        rw [usize_sub_one_toNat hp]; omega)
    let bN := if d.two then h1 else h0
    if bN == (if d.two then g1 else g0) then
      setBoundsU P hP2 D nW hi hhi h0 h1 g0 g1 ds hds (i + 1) tree htree pending hpend
    else if pH == floatZero then
      setBoundsU P hP2 D nW hi hhi h0 h1 g0 g1 ds hds (i + 1) tree htree pending hpend
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
        · rw [fixUntilGo_size P _ D rfl]; exact htree
      setBoundsU P hP2 D nW hi hhi h0 h1 g0 g1 ds hds (i + 1)
        (tree'.uset leaf (d.rate * (bN * pH)) (by omega)) (by rw [size_uset]; exact htree') leaf
        (Or.inr (by omega))
  else if hz : pending = 0 then tree
    else Gen16.fixPathGo P D tree htree pending (hpend.resolve_left hz)
      (tree.uget pending (by have := hpend.resolve_left hz; omega))
termination_by ds.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize ds i h]; omega)

theorem setBoundsU_size (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (nW : USize)
    (hi : FloatArray) (hhi : nW.toNat ≤ hi.size) (h0 h1 g0 g1 : Float) (ds : Array DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat) :
    ∀ m (i : USize), ds.size - i.toNat = m → ∀ (tree : FloatArray)
      (htree : 2 * P.toNat ≤ tree.size) (pending : USize) hpend,
      (setBoundsU P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend).size =
        tree.size := by
  intro m
  induction m with
  | zero =>
    intro i hm tree htree pending hpend
    have hge : ¬ i < ds.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize ds i h; omega
    rw [setBoundsU, dite_eq_right hge]
    split
    · rfl
    · rw [fixPathGo_size P _ D rfl]
  | succ m ih =>
    intro i hm tree htree pending hpend
    by_cases h : i < ds.usize
    · have hs := Gen15.succ_toNat_of_lt_usize ds i h
      rw [setBoundsU, dite_eq_left h]
      dsimp only
      repeat' split
      all_goals first
        | exact ih (i + 1) (by omega) _ _ _ _
        | (rw [ih (i + 1) (by omega), size_uset, fixUntilGo_size P _ D rfl])
        | (rw [ih (i + 1) (by omega), size_uset])
    · rw [setBoundsU, dite_eq_right h]
      split
      · rfl
      · rw [fixPathGo_size P _ D rfl]

/-- The sizes the driver carries: the brackets cover the species, the tree the leaves. -/
def Sized (nW P : USize) (c : CacheV) : Prop :=
  c.lo.size = nW.toNat ∧ c.hi.size = nW.toNat ∧ c.tree.size = 2 * P.toNat

/-- Generation 19's `rebracketV` with its accesses proved in bounds. -/
@[inline] def rebracketU (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
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
  ⟨lo, hi, setBoundsU P hP2 D nW hi (by rw [size_uset]; exact Nat.le_of_eq hc.2.1.symm) hiN (ff2 hiN) hiS (ff2 hiS)
    (W.deps.uget s (by omega)) (fun k h => hB.depKP s.toNat (by omega) k h) 0 c.tree
    (Nat.le_of_eq hc.2.2.symm) 0 (Or.inl rfl)⟩

theorem rebracketU_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (c : CacheV) (hc : Sized nW P c) (s : USize)
    (hs : s.toNat < nW.toNat) :
    Sized nW P (rebracketU W P hP2 D nW numRx rates hB pop hpop c hc s hs) := by
  refine ⟨?_, ?_, ?_⟩
  · show (c.lo.uset _ _ _).size = nW.toNat
    rw [size_uset]; exact hc.1
  · show (c.hi.uset _ _ _).size = nW.toNat
    rw [size_uset]; exact hc.2.1
  · show (setBoundsU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).size = 2 * P.toNat
    rw [setBoundsU_size _ _ _ _ _ _ _ _ _ _ _ _ _ 0 rfl]
    exact hc.2.2

/-- Generation 19's `refreshFromV` with its accesses proved in bounds. -/
def refreshFromU (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates)
    (chs : Array ChangeW) (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (i : USize) (c : CacheV)
    (hc : Sized nW P c) : CacheV :=
  if h : i < chs.usize then
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    let s := (chs.uget i hi').species
    have hs : s.toNat < nW.toNat := hchs i.toNat hi'
    have hms := hB.ms
    if staleW (W.ms.uget s (by omega)) (pop.uget s (by omega)) (c.lo.uget s (by have := hc.1; omega))
        (c.hi.uget s (by have := hc.2.1; omega)) then
      refreshFromU W P hP2 D nW numRx rates hB chs hchs pop hpop (i + 1)
        (rebracketU W P hP2 D nW numRx rates hB pop hpop c hc s hs)
        (rebracketU_sized W P hP2 D nW numRx rates hB pop hpop c hc s hs)
    else refreshFromU W P hP2 D nW numRx rates hB chs hchs pop hpop (i + 1) c hc
  else c
termination_by chs.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize chs i h]; omega)

theorem refreshFromU_sized (W : Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Bounds W nW P numRx rates)
    (chs : Array ChangeW) (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ (c : CacheV) (hc : Sized nW P c),
      Sized nW P (refreshFromU W P hP2 D nW numRx rates hB chs hchs pop hpop i c hc) := by
  intro m
  induction m with
  | zero =>
    intro i hm c hc
    have hge : ¬ i < chs.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize chs i h; omega
    rw [refreshFromU, dite_eq_right hge]
    exact hc
  | succ m ih =>
    intro i hm c hc
    by_cases h : i < chs.usize
    · have hs := Gen15.succ_toNat_of_lt_usize chs i h
      rw [refreshFromU, dite_eq_left h]
      dsimp only
      split
      · exact ih (i + 1) (by omega) _ _
      · exact ih (i + 1) (by omega) _ _
    · rw [refreshFromU, dite_eq_right h]
      exact hc

/-! ## The driver -/

/-- Generation 19's driver with every access in bounds by proof and no tree size test. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Compiled) (msN : Array Nat) (n : Nat)
    (hms : msN.size = n) (hval : Gen15.ValidChanges C n) (nW : USize) (numRx : USize) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Bounds W nW P numRx rates) (horizon : Float) (save : Bool) (cap : USize)
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
                have hjr : j.toNat < rates.size := by have := hB.rates; have : j.toNat < numRx.toNat := hj; omega
                have hjf : j.toNat < W.factors.size := by
                  have := hB.factors; have : j.toNat < numRx.toNat := hj; omega
                have hst : (W.factors.uget j hjf).s.toNat < nW.toNat ∧
                    (W.factors.uget j hjf).t.toNat < nW.toNat := hB.factorST j.toNat hjf
                let threshold := v * c.tree.uget k (by omega)
                let actual := rates.uget j hjr *
                  evalU (W.factors.uget j hjf) pop (by have := hst.1; omega) (by have := hst.2; omega)
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
                have hjc : j.toNat < W.changes.size := by
                  have := hB.changes; have : j.toNat < numRx.toNat := hj; omega
                let chs := W.changes.uget j hjc
                have hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat :=
                  fun k h => hB.changeS j.toNat hjc k h
                let p := applyU chs nW hchs W.ms c.lo c.hi hB.ms (Nat.le_of_eq hc.1.symm)
                  (Nat.le_of_eq hc.2.1.symm) 0 pop (by omega) false
                have hp : p.size = nW.toNat + 1 := by
                  rw [applyU_size chs nW hchs W.ms c.lo c.hi hB.ms (Nat.le_of_eq hc.1.symm)
                    (Nat.le_of_eq hc.2.1.symm) _ 0 rfl]; exact hpop
                if p.uget nW (by omega) == floatZero then
                  let trace := if save then trace.push (time, ⟨ofCounts p n, ofCounts c.lo n,
                    ofCounts c.hi n⟩) else trace
                  run C codes W msN n hms hval nW numRx P hP2 D rates hB horizon save cap
                    (evFuel - 1) cap p hp c hc time total floatZero rng.s0 rng.s1 rng.s2 rng.s3
                    (count + 1) trace
                else if smallU chs nW hchs p (by omega) 0 then
                  let c' := refreshFromU W P hP2 D nW numRx rates hB chs hchs p (by omega) 0 c hc
                  have hc' : Sized nW P c' :=
                    refreshFromU_sized W P hP2 D nW numRx rates hB chs hchs p (by omega) _ 0 rfl c hc
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
                    run C codes W msN n hms hval nW numRx P hP2 D rates hB horizon save cap
                      (evFuel - 1) cap p hp c' hc' time total floatZero rng.s0 rng.s1 rng.s2
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
              run C codes W msN n hms hval nW numRx P hP2 D rates hB horizon save cap evFuel
                (prFuel - 1) pop hpop c hc now total elapsed rng.s0 rng.s1 rng.s2 rng.s3 count trace
termination_by (evFuel.toNat, prFuel.toNat)
decreasing_by
  all_goals first
    | (have : evFuel.toNat ≠ 0 := fun h => he (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat evFuel he]; exact Prod.Lex.left _ _ (by omega))
    | (have : prFuel.toNat ≠ 0 := fun h => _hz (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat prFuel _hz]; exact Prod.Lex.right _ (by omega))

/-- Generation 19's start, entering generation 20's driver when the compiled records' bounds
also hold, and otherwise generation 19's start. -/
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
        C.gen5.base.factors.all (FactorW.ok n) = true ∧
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
        cV.hi.size = n.toUSize.toNat ∧ cV.tree.size = 2 * C.gen5.base.leaves.toUSize.toNat then
      run C codes W C.gen5.base.ms n rfl (Gen15.validChanges_spec hs.1.2.2.2.1) n.toUSize
        C.gen5.base.numRx.toUSize C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h.2.2)
        C.gen5.base.depth.toUSize C.gen5.base.rates (boundsOK_spec hs.2.1) horizon save
        cap.toUSize fuel.toUSize cap.toUSize popW hs.2.2.1 cV ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩
        now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize trace
    else Gen19.start C codes horizon save cap fuel pop c now rng count trace
  else Gen19.start C codes horizon save cap fuel pop c now rng count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(Gen7.finite start && Gen7.finite horizon && decide (start ≤ horizon)) then
    .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen6.compile net
    Gen20.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen20
