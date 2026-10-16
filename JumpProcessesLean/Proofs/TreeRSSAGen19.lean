import JumpProcessesLean.Proofs.TreeRSSAGen18
import JumpProcessesLean.Proofs.FloatOrder
import JumpProcessesLean.TreeRSSA.Gen19

/-!
# Generation 19 is generation 17, hence the specification

Generation 19 is generation 18 without the lower bounds. Its state is related to generation 17's
as generation 18's is (`Rel18`), with generation 17's lower bounds in place of the missing ones,
and generation 17's state keeps two invariants: the cached lower bounds are the propensities at
the brackets' lower ends (`CacheOK`, preserved by every firing through the chain of earlier
generations' firings), and no species is outside its bracket (`NoStale`, `fire17`). Then each
lower bound is the rate times the integer factor at the lower ends, at most the factor at the
counts, and the lower-bound test accepts only proposals that the exact test accepts
(`squeeze_redundant`): generation 17's acceptance is generation 19's (`acc19_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)
open JumpProcessesLean.TreeRSSA.Gen7 (floatInf floatNegInf)
open JumpProcessesLean.Proofs.Counts

/-! ## Refreshes without lower bounds -/

/-- Generation 19's cache is generation 18's without the lower bounds. -/
def projV (c : Gen18.CacheW) : Gen19.CacheV := ⟨c.lo, c.hi, c.tree⟩

theorem setBoundsV_proj (leaves P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (lo hi : FloatArray) (l0 l1 m0 m1 h0 h1 g0 g1 : Float) (ds : Array Gen18.DepW) :
    ∀ m (i : USize), ds.size - i.toNat = m → ∀ (lower tree : FloatArray) (pending : USize),
      Gen19.setBoundsV leaves P hP2 D hi h0 h1 g0 g1 ds i tree pending =
        (Gen18.setBoundsW leaves P hP2 D lo hi l0 l1 m0 m1 h0 h1 g0 g1 ds i lower tree
          pending).2 := by
  intro m
  induction m with
  | zero =>
    intro i hm lower tree pending
    have hge : ¬ i < ds.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize ds i h; omega
    rw [Gen19.setBoundsV, dite_eq_right hge, Gen18.setBoundsW, dite_eq_right hge]
  | succ m ih =>
    intro i hm lower tree pending
    by_cases h : i < ds.usize
    · have hs := Gen15.succ_toNat_of_lt_usize ds i h
      rw [Gen19.setBoundsV, dite_eq_left h, Gen18.setBoundsW, dite_eq_left h]
      dsimp only
      split_ifs <;> exact ih _ (by omega) _ _ _
    · rw [Gen19.setBoundsV, dite_eq_right h, Gen18.setBoundsW, dite_eq_right h]

theorem rebracketV_proj (W : Gen18.Compiled) (leaves P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (pop : FloatArray) (cW : Gen18.CacheW) (s : USize) :
    Gen19.rebracketV W leaves P hP2 D pop (projV cW) s =
      projV (Gen18.rebracketW W leaves P hP2 D pop cW s) := by
  simp only [Gen19.rebracketV, Gen18.rebracketW, projV]
  congr 1
  exact setBoundsV_proj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 rfl _ _ _

theorem refreshFromV_proj (W : Gen18.Compiled) (leaves P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (chs : Array Gen18.ChangeW) (pop : FloatArray) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ cW : Gen18.CacheW,
      Gen19.refreshFromV W leaves P hP2 D chs pop i (projV cW) =
        projV (Gen18.refreshFrom W leaves P hP2 D chs pop i cW) := by
  intro m
  induction m with
  | zero =>
    intro i hm cW
    have hge : ¬ i < chs.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize chs i h; omega
    rw [Gen19.refreshFromV, dite_eq_right hge, Gen18.refreshFrom, dite_eq_right hge]
  | succ m ih =>
    intro i hm cW
    by_cases h : i < chs.usize
    · have hs := Gen15.succ_toNat_of_lt_usize chs i h
      rw [Gen19.refreshFromV, dite_eq_left h, Gen18.refreshFrom, dite_eq_left h]
      dsimp only
      by_cases hst : Gen18.staleW (Gen18.cget W.ms (chs.uget i (Gen15.lt_size_of_lt_usize chs i h)).species)
          (Gen18.cget pop (chs.uget i (Gen15.lt_size_of_lt_usize chs i h)).species)
          (Gen18.cget cW.lo (chs.uget i (Gen15.lt_size_of_lt_usize chs i h)).species)
          (Gen18.cget cW.hi (chs.uget i (Gen15.lt_size_of_lt_usize chs i h)).species) = true
      · rw [ite_eq_left (show Gen18.staleW _ _ (Gen18.cget (projV cW).lo _) (Gen18.cget (projV cW).hi _) = true
          from hst), ite_eq_left hst, rebracketV_proj]
        exact ih _ (by omega) _
      · rw [ite_eq_right (show ¬ Gen18.staleW _ _ (Gen18.cget (projV cW).lo _) (Gen18.cget (projV cW).hi _) = true
          from hst), ite_eq_right hst]
        exact ih _ (by omega) _
    · rw [Gen19.refreshFromV, dite_eq_right h, Gen18.refreshFrom, dite_eq_right h]

/-! ## Generation 17's lower bounds -/

theorem fire13_cacheOK (net : Network Float) (hwf : ReactantsInRange net) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (pop : Array Nat) (c : Cache) (hc : CacheOK net c) (j : Nat) :
    CacheOK net (Gen13.fire (Gen6.compile net) (Gen13.codesOf (Gen6.compile net).gen5) P hP2
      (Gen6.compile net).gen5.base.ms pop c j).2 := by
  rw [fire13_eq _ (gen5_depFactors_size net) P hP2, fire12_eq, gen9_fire_eq, gen7_fire_eq,
    gen6_fire_eq _ net rfl]
  show CacheOK net (Gen5.fire (Gen5.compile net) pop c j).2
  rw [gen5_fire_eq net hwf pop c hc j]
  exact (gen3_fire_ok net hwf pop c hc j).2

theorem lowerOf_eq (net : Network Float) (c : Cache) (hc : CacheOK net c) :
    Gen19.lowerOf (Gen6.compile net) c.lo = c.lower := by
  show FloatArray.mk (net.reactions.map fun rx => propensity hostArithmetic rx c.lo) = c.lower
  rw [← hc.1]

theorem lower_get (net : Network Float) (c : Cache) (hc : CacheOK net c) (j : USize)
    (hj : j.toNat < net.reactions.size) :
    Gen17.fget c.lower j = Gen17.fget (Gen6.compile net).gen5.base.rates j *
      natToFloat ((Gen17.aget (Gen6.compile net).gen5.base.factors j).eval c.lo) := by
  rw [← lowerOf_eq net c hc, fget_eq, fget_eq, aget_eq]
  show (net.reactions.map fun rx => Gen2.rate rx c.lo)[j.toNat]! =
    (net.reactions.map (·.rate))[j.toNat]! *
      natToFloat ((net.reactions.map fun rx => Gen3.Factor.compile rx.reactants)[j.toNat]!.eval c.lo)
  rw [getElem!_pos _ j.toNat (by simpa using hj), getElem!_pos _ j.toNat (by simpa using hj),
    getElem!_pos _ j.toNat (by simpa using hj), Array.getElem_map, Array.getElem_map,
    Array.getElem_map, factor_eval_compile]
  rfl

/-! ## Monotone factors -/

theorem eval_mono (n : Nat) (f : Gen3.Factor) (hf : Gen18.FactorW.ok n f = true)
    (lo pop : Array Nat) (h : ∀ t < n, lo[t]! ≤ pop[t]!) : f.eval lo ≤ f.eval pop := by
  cases f with
  | one s =>
    simp only [Gen18.FactorW.ok, decide_eq_true_eq] at hf
    exact h s hf
  | two s =>
    simp only [Gen18.FactorW.ok, decide_eq_true_eq] at hf
    have := h s hf
    exact Nat.mul_le_mul this (Nat.sub_le_sub_right this 1)
  | pair s ν t μ =>
    simp only [Gen18.FactorW.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
    obtain ⟨⟨⟨hs, ht⟩, rfl⟩, rfl⟩ := hf
    simp only [Gen3.Factor.eval, Gen3.ff, ite_eq_left]
    exact Nat.mul_le_mul (h s hs) (h t ht)
  | general rs => simp [Gen18.FactorW.ok] at hf

theorem eval_lt (n : Nat) (f : Gen3.Factor) (hf : Gen18.FactorW.ok n f = true)
    (pop : Array Nat) (h : ∀ t < n, pop[t]! < 2 ^ 26) : f.eval pop < 2 ^ 53 := by
  cases f with
  | one s =>
    simp only [Gen18.FactorW.ok, decide_eq_true_eq] at hf
    have := h s hf
    show pop[s]! < 2 ^ 53
    omega
  | two s =>
    simp only [Gen18.FactorW.ok, decide_eq_true_eq] at hf
    have := h s hf
    show pop[s]! * (pop[s]! - 1) < 2 ^ 53
    calc pop[s]! * (pop[s]! - 1) ≤ pop[s]! * pop[s]! := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ < 2 ^ 26 * 2 ^ 26 := Nat.mul_lt_mul'' this this
      _ ≤ 2 ^ 53 := by norm_num
  | pair s ν t μ =>
    simp only [Gen18.FactorW.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
    obtain ⟨⟨⟨hs, ht⟩, rfl⟩, rfl⟩ := hf
    simp only [Gen3.Factor.eval, Gen3.ff, ite_eq_left]
    calc pop[s]! * pop[t]! < 2 ^ 26 * 2 ^ 26 := Nat.mul_lt_mul'' (h s hs) (h t ht)
      _ ≤ 2 ^ 53 := by norm_num
  | general rs => simp [Gen18.FactorW.ok] at hf

theorem noStale_le {ms pop lo hi : Array Nat} {n : Nat} (h : NoStale ms pop lo hi n) :
    ∀ t < n, lo[t]! ≤ pop[t]! := by
  intro t ht
  have := h t ht
  rw [staleI_eq] at this
  simp only [decide_eq_false_iff_not, not_or] at this
  omega

/-! ## The driver -/

/-- What generation 19's driver needs of the network: generation 18's conditions, the network's
compiled form, changes that add or remove, and rates `0 ≤ r < 2^52`. -/
structure Static19 (net : Network Float) (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (n : Nat) : Prop where
  s18 : Static18 C codes P n
  hwf : ReactantsInRange net
  codes : codes = Gen13.codesOf C.gen5
  exclusive : ∀ j : Nat, ∀ ch ∈ (C.changes[j]!).toList, ch.up = 0 ∨ ch.down = 0
  rates : ∀ j < C.gen5.base.numRx, decide (floatZero ≤ C.gen5.base.rates.get! j) = true ∧
    decide (C.gen5.base.rates.get! j < Float.ofNat (2 ^ 52)) = true

/-- Generation 19's state holds generation 17's, whose lower bounds are the propensities at the
brackets' lower ends and whose counts are inside their brackets. -/
structure Rel19 (net : Network Float) (C : Gen6.Compiled) (n : Nat) (popW : FloatArray)
    (cV : Gen19.CacheV) (pop : Array Nat) (c : Cache) : Prop where
  rel : Rel18 n popW ⟨cV.lo, cV.hi, c.lower, cV.tree⟩ pop c
  ok : CacheOK net c
  noStale : NoStale C.gen5.base.ms pop c.lo c.hi n

theorem lowerOf_eq' (net : Network Float) (C : Gen6.Compiled) (hC : C = Gen6.compile net)
    (c : Cache) (hc : CacheOK net c) : Gen19.lowerOf C c.lo = c.lower := by
  subst hC; exact lowerOf_eq net c hc

theorem descendW19_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      Gen19.descendW tree P hP hP2 k hk0 x = Gen17.descendW tree P hP hP2 k hk0 x := by
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
      Gen17.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
  | succ m ih =>
    intro k hk0 x hm
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [Gen19.descendW, dite_eq_left_of_eq_true (eq_true hkP),
        Gen17.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega)
    · rw [Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
        Gen17.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]

theorem descendW19_eq' (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) :
    Gen19.descendW tree P hP hP2 k hk0 x = Gen17.descendW tree P hP hP2 k hk0 x :=
  descendW19_eq tree P hP hP2 _ k hk0 x le_rfl

theorem hmono19 {net : Network Float} {C : Gen6.Compiled} {codes : Array (Array Nat)} {P : USize}
    {n : Nat} {numRx : USize} (hS : Static19 net C codes P n)
    (hnum : numRx.toNat = C.gen5.base.numRx) {popW : FloatArray} {cV : Gen19.CacheV}
    {pop : Array Nat} {c : Cache} (hrel : Rel19 net C n popW cV pop c) :
    ∀ j : USize, j < numRx →
      (Gen17.aget C.gen5.base.factors j).eval c.lo ≤ (Gen17.aget C.gen5.base.factors j).eval pop := by
  intro j hj
  have hjf : j.toNat < C.gen5.base.factors.size := by
    rw [hS.s18.numFactors, ← hnum]; exact hj
  rw [aget_eq]
  exact eval_mono n _ (hS.s18.factors _ hjf) c.lo pop (noStale_le hrel.noStale)

theorem hlt19 {net : Network Float} {C : Gen6.Compiled} {codes : Array (Array Nat)} {P : USize}
    {n : Nat} {numRx : USize} (hS : Static19 net C codes P n)
    (hnum : numRx.toNat = C.gen5.base.numRx) {popW : FloatArray} {cV : Gen19.CacheV}
    {pop : Array Nat} {c : Cache} (hrel : Rel19 net C n popW cV pop c) :
    ∀ j : USize, j < numRx → (Gen17.aget C.gen5.base.factors j).eval pop < 2 ^ 53 := by
  intro j hj
  have hjf : j.toNat < C.gen5.base.factors.size := by
    rw [hS.s18.numFactors, ← hnum]; exact hj
  rw [aget_eq]
  exact eval_lt n _ (hS.s18.factors _ hjf) pop hrel.rel.small

theorem hrates19 {net : Network Float} {C : Gen6.Compiled} {codes : Array (Array Nat)} {P : USize}
    {n : Nat} {numRx : USize} (hS : Static19 net C codes P n)
    (hnum : numRx.toNat = C.gen5.base.numRx) :
    ∀ j : USize, j < numRx →
      decide (floatZero ≤ Gen17.fget C.gen5.base.rates j) = true ∧
      decide (Gen17.fget C.gen5.base.rates j < Float.ofNat (2 ^ 52)) = true := by
  intro j hj
  rw [fget_eq]
  exact hS.rates _ (by have : j.toNat < numRx.toNat := hj; omega)

/-- With the lower bounds the propensities at the lower ends, generation 17's acceptance is
generation 19's. -/
theorem acc19_eq (net : Network Float) (C : Gen6.Compiled) (hC : C = Gen6.compile net)
    (codes : Array (Array Nat)) (numRx : USize) (hnum : numRx.toNat = C.gen5.base.numRx)
    (popW : FloatArray) (pop : Array Nat) (c : Cache) (hc : CacheOK net c)
    (hfg : ∀ j : USize, j < numRx →
      Gen18.evalW (Gen17.aget (Gen18.compileW C codes).factors j) popW =
        natToFloat ((Gen17.aget C.gen5.base.factors j).eval pop))
    (hmono : ∀ j : USize, j < numRx →
      (Gen17.aget C.gen5.base.factors j).eval c.lo ≤ (Gen17.aget C.gen5.base.factors j).eval pop)
    (hlt : ∀ j : USize, j < numRx → (Gen17.aget C.gen5.base.factors j).eval pop < 2 ^ 53)
    (hrates : ∀ j : USize, j < numRx →
      decide (floatZero ≤ Gen17.fget C.gen5.base.rates j) = true ∧
      decide (Gen17.fget C.gen5.base.rates j < Float.ofNat (2 ^ 52)) = true)
    (j : USize) (t : Float) :
    (if (!decide (j < numRx)) = true then false
     else decide (floatZero < Gen17.fget C.gen5.base.rates j *
            Gen18.evalW (Gen17.aget (Gen18.compileW C codes).factors j) popW) &&
          decide (t ≤ Gen17.fget C.gen5.base.rates j *
            Gen18.evalW (Gen17.aget (Gen18.compileW C codes).factors j) popW)) =
    (if (!decide (j < numRx)) = true then false
     else if (decide (floatZero < Gen17.fget c.lower j) && decide (t ≤ Gen17.fget c.lower j)) = true
       then true
     else decide (floatZero < Gen17.fget C.gen5.base.rates j *
            natToFloat ((Gen17.aget C.gen5.base.factors j).eval pop)) &&
          decide (t ≤ Gen17.fget C.gen5.base.rates j *
            natToFloat ((Gen17.aget C.gen5.base.factors j).eval pop))) := by
  by_cases hj : j < numRx
  · have hjn : j.toNat < net.reactions.size := by
      have : j.toNat < numRx.toNat := hj
      rw [hnum, hC] at this; exact this
    simp only [hj, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have hl := hlt j hj
    have hm := hmono j hj
    have hr := hrates j hj
    rw [hfg j hj]
    subst hC
    rw [lower_get net c hc j hjn, natToFloat_eq _ (by omega), natToFloat_eq _ (by omega)]
    exact (squeeze_redundant hr.1 hr.2 hm hl).symm
  · simp [hj]

/-- Generation 17's firing keeps its invariants: no species outside its bracket, and the lower
bounds the propensities at the lower ends. -/
theorem fire19 (net : Network Float) (C : Gen6.Compiled) (hC : C = Gen6.compile net)
    (codes : Array (Array Nat)) (n : Nat) (hms : C.gen5.base.ms.size = n)
    (hval : Gen15.ValidChanges C n) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (hS : Static19 net C codes P n) (c : Cache) (hlo : c.lo.size = n) (hhi : c.hi.size = n)
    (pop : Array Nat) (hpop : pop.size = n) {popW : FloatArray} {cV : Gen19.CacheV}
    (hrel : Rel19 net C n popW cV pop c) (j : USize) :
    ((Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
        C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = n →
      NoStale C.gen5.base.ms (Gen17.applyTest (Gen17.changesAt C n hval j).1 n
        (Gen17.changesAt C n hval j).2 C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false)
        c.lo c.hi n) ∧
    ((Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
        C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size ≠ n →
      NoStale C.gen5.base.ms (Gen17.applyTest (Gen17.changesAt C n hval j).1 n
          (Gen17.changesAt C n hval j).2 C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).pop
        ((Gen17.changesAt C n hval j).1.foldl (fun d ch => Gen16.refresh C.gen5 codes P hP2
          C.gen5.base.ms (Gen17.applyTest (Gen17.changesAt C n hval j).1 n
            (Gen17.changesAt C n hval j).2 C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop
            false).pop d ch.species) c).lo
        ((Gen17.changesAt C n hval j).1.foldl (fun d ch => Gen16.refresh C.gen5 codes P hP2
          C.gen5.base.ms (Gen17.applyTest (Gen17.changesAt C n hval j).1 n
            (Gen17.changesAt C n hval j).2 C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop
            false).pop d ch.species) c).hi n ∧
      CacheOK net ((Gen17.changesAt C n hval j).1.foldl (fun d ch => Gen16.refresh C.gen5 codes P
        hP2 C.gen5.base.ms (Gen17.applyTest (Gen17.changesAt C n hval j).1 n
          (Gen17.changesAt C n hval j).2 C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop
          false).pop d ch.species) c)) := by
  have hcv := changesAt_val C n hval j
  obtain ⟨F1, F2, F3⟩ := fire17 C codes P hP2 n hms j.toNat (Gen17.changesAt C n hval j).1 hcv
    (Gen17.changesAt C n hval j).2 (by rw [hcv]; exact hS.s18.changesSmall _)
    (by rw [hcv]; exact hS.exclusive _) (by rw [hcv]; exact hS.s18.nodup _)
    pop hpop c hlo hhi hrel.noStale
  have hok := hrel.ok
  have hwf := hS.hwf
  have hcodes := hS.codes
  refine ⟨fun hps => ?_, fun hps => ?_⟩
  · obtain ⟨h1, h2⟩ := F1 hps
    rw [← h1, ← h2] at F3
    exact F3
  · obtain ⟨h1, h2⟩ := F2 hps
    rw [← h1, ← h2] at F3
    refine ⟨F3, ?_⟩
    rw [h2]
    subst hC hcodes
    exact fire13_cacheOK net hwf P hP2 pop c hok j.toNat

theorem run19_eq_of (net : Network Float) (C : Gen6.Compiled) (hC : C = Gen6.compile net)
    (codes : Array (Array Nat)) (n : Nat)
    (hms : C.gen5.base.ms.size = n) (hval : Gen15.ValidChanges C n)
    (P : USize) (hP2 : 2 * P.toNat < USize.size) (numRx : USize)
    (hnum : numRx.toNat = C.gen5.base.numRx) (hS : Static19 net C codes P n)
    (horizon : Float) (save : Bool) (cap : USize) (fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ (evW prW : USize) popW cW pop hpop c hlo hhi now total elapsed s0 s1
      s2 s3 (count : USize) trace, evW.toNat = f → Rel19 net C n popW cW pop c →
      Gen19.run C codes (Gen18.compileW C codes) C.gen5.base.ms n hms hval n.toUSize numRx P hP2
          C.gen5.base.depth.toUSize C.gen5.base.rates horizon save cap evW prW popW cW now total elapsed
          s0 s1 s2 s3 count trace =
        Gen17.run C codes C.gen5.base.ms n hms hval numRx P hP2 C.gen5.base.rates C.gen5.base.factors
          horizon save cap evW prW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel (evW prW : USize) popW cW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = fuel → prW.toNat = prFuel → Rel19 net C n popW cW pop c →
      Gen19.run C codes (Gen18.compileW C codes) C.gen5.base.ms n hms hval n.toUSize numRx P hP2
          C.gen5.base.depth.toUSize C.gen5.base.rates horizon save cap evW prW popW cW now total elapsed
          s0 s1 s2 s3 count trace =
        Gen17.run C codes C.gen5.base.ms n hms hval numRx P hP2 C.gen5.base.rates C.gen5.base.factors
          horizon save cap evW prW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro evW prW popW cW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace hev hpr _
    have h0 : prW = 0 := USize.toNat_inj.mp (by rw [hpr]; rfl)
    rw [Gen19.run, dite_eq_left h0, Gen17.run, dite_eq_left h0]
  | succ pf ih =>
    intro evW prW popW cW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace hev hpr hrel
    have hnU := hS.s18.nU
    have hnW : n.toUSize.toNat = n := toUSize_toNat_of_lt (by omega)
    have hcounts : Gen18.ofCounts popW n = pop :=
      ofCounts_eq hrel.rel.counts (fun t ht => by have := hrel.rel.small t ht; omega)
    have hclo : Gen18.ofCounts cW.lo n = c.lo :=
      ofCounts_eq hrel.rel.cache.lo (fun t ht => by have := hrel.rel.cache.loSmall t ht; omega)
    have hchi : Gen18.ofCounts cW.hi n = c.hi :=
      ofCounts_eq hrel.rel.cache.hi (fun t ht => by have := hrel.rel.cache.hiSmall t ht; omega)
    obtain ⟨loW, hiW, treeW⟩ := cW
    have htreeR : treeW = c.tree := hrel.rel.cache.tree
    subst htreeR
    rw [Gen19.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen17.run,
      dite_eq_right (usize_ne_zero_of_toNat hpr)]
    by_cases hT : 2 * P ≤ c.tree.usize
    · rw [dite_eq_left hT, dite_eq_left hT]
      dsimp only
      generalize hU : Xoshiro.uniform ⟨s0, s1, s2, s3⟩ = U
      obtain ⟨u, r1⟩ := U
      dsimp only
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      generalize hE : r1.exponential = E
      obtain ⟨e, r2⟩ := E
      dsimp only
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      generalize hV : r2.uniform = V
      obtain ⟨v, r3⟩ := V
      dsimp only
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      simp only [descendW19_eq']
      have hevW : ∀ j : USize, j < numRx →
          Gen18.evalW (Gen17.aget (Gen18.compileW C codes).factors j) popW =
            natToFloat ((Gen17.aget C.gen5.base.factors j).eval pop) := by
        intro j hj
        have hjf : j.toNat < C.gen5.base.factors.size := by
          rw [hS.s18.numFactors, ← hnum]; exact hj
        rw [aget_eq, aget_eq, compileW_factors C codes _ hjf]
        exact evalW_eq _ n (hS.s18.factors _ hjf) (by omega) pop popW hrel.rel.counts hrel.rel.small
      rw [acc19_eq net C hC codes numRx hnum popW pop c hrel.ok hevW (hmono19 hS hnum hrel)
        (hlt19 hS hnum hrel) (hrates19 hS hnum)]
      refine ite_congr rfl (fun hacc => ?_) (fun _ => ?_)
      · have hjn : Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
            Gen11.usize_one_pos (u * total) - P < numRx := by
          by_contra hj
          rw [ite_eq_left (by simp [hj])] at hacc
          cases hacc
        have hclo' : Gen18.ofCounts loW n = c.lo := hclo
        have hchi' : Gen18.ofCounts hiW n = c.hi := hchi
        refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
        refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
        refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
        refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
        · rw [hcounts, hclo', hchi']
        · refine dite_congr rfl (fun _ => rfl) (fun he => ?_)
          have hchW : ∀ j : USize, j < numRx → Gen17.aget (Gen18.compileW C codes).changes j =
              (Gen17.changesAt C n hval j).1.map Gen18.ChangeW.ofChange := by
            intro j hj
            have hjc : j.toNat < C.changes.size := by
              have := hS.s18.numChanges; have : j.toNat < numRx.toNat := hj; omega
            rw [aget_eq, compileW_changes C codes _ hjc, changesAt_val]
          simp only [hchW _ hjn]
          obtain ⟨f1, f2, f3, f4, f5, f6⟩ := fire18 C codes n hms hval P hS.s18 popW loW hiW pop hpop c hlo hhi
            hrel.rel (Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
              Gen11.usize_one_pos (u * total) - P)
          obtain ⟨g1, g2⟩ := fire19 net C hC codes n hms hval P hP2 hS c hlo hhi pop hpop hrel
            (Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
              Gen11.usize_one_pos (u * total) - P)
          simp only [f3, decide_eq_true_eq]
          by_cases hps : (Gen17.applyTest (Gen17.changesAt C n hval (Gen17.descendW c.tree P
              (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1 n
              (Gen17.changesAt C n hval (Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT)
                hP2 1 Gen11.usize_one_pos (u * total) - P)).2
              C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = n
          · rw [ite_eq_left hps, dite_eq_left hps]
            have f1' := f1
            rw [ite_eq_left hps] at f1'
            rw [ofCounts_eq f1' (fun t ht => by have := f5 hps t ht; omega), hclo', hchi']
            have hev0 : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
            obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            exact hnext f hf (evW - 1) cap _ ⟨loW, hiW, c.tree⟩ _ hps c hlo hhi _ total floatZero _ _ _ _
              (count + 1) _ (by rw [Gen16.pred_toNat evW he]; omega)
              ⟨⟨f1', f2, f5 hps, hrel.rel.cache⟩, hrel.ok, g1 hps⟩
          · rw [ite_eq_right hps, dite_eq_right hps]
            have f1' := f1
            rw [ite_eq_right hps] at f1'
            have hpp : Gen18.ofCounts (Gen18.applyW ((Gen17.changesAt C n hval (Gen17.descendW c.tree P
                (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1.map
                Gen18.ChangeW.ofChange) (Gen18.compileW C codes).ms loW hiW n.toUSize 0 popW false) n =
                (Gen17.applyTest (Gen17.changesAt C n hval (Gen17.descendW c.tree P
                  (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1 n
                  (Gen17.changesAt C n hval (Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT)
                    hP2 1 Gen11.usize_one_pos (u * total) - P)).2
                  C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).pop := by
              have h4 := f4
              simp only [ite_eq_right hps] at h4
              exact ofCounts_eq f1' (fun t ht => by have := h4 t ht; omega)
            have hcsz : (Gen17.changesAt C n hval (Gen17.descendW c.tree P
                (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1.size <
                USize.size := by rw [changesAt_val]; exact hS.s18.changesSmall _
            by_cases hsf : Gen18.smallFrom ((Gen17.changesAt C n hval (Gen17.descendW c.tree P
                (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1.map
                Gen18.ChangeW.ofChange) (Gen18.applyW ((Gen17.changesAt C n hval (Gen17.descendW c.tree P
                (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1.map
                Gen18.ChangeW.ofChange) (Gen18.compileW C codes).ms loW hiW n.toUSize 0 popW false) 0 = true
            · rw [ite_eq_left hsf]
              have h4 := f4
              simp only [ite_eq_right hps] at h4
              have hsm25 := smallFrom_spec _ n (Gen17.changesAt C n hval _).2 hcsz (by omega) _ _ f1'
                (fun t ht => by have := h4 t ht; omega) _ 0 rfl hsf
              simp only [USize.toNat_zero, List.drop_zero] at hsm25
              have hR := refreshFrom_eq C codes P hP2 hS.s18.leaves hS.s18.depth n hS.s18.nU hms
                hS.s18.msSmall hS.s18.deps _ (Gen17.changesAt C n hval _).2 hcsz _ _ f1' hsm25 _ 0 rfl c
                ⟨loW, hiW, c.lower, c.tree⟩ hrel.rel.cache
              simp only [USize.toNat_zero, List.drop_zero, Array.foldl_toList] at hR
              rw [show (⟨loW, hiW, c.tree⟩ : Gen19.CacheV) = projV ⟨loW, hiW, c.lower, c.tree⟩ from rfl,
                refreshFromV_proj _ _ _ _ _ _ _ _ 0 rfl]
              simp only [projV]
              have e3 := ofCounts_eq hR.lo (fun t ht => by have := hR.loSmall t ht; omega)
              have e4 := ofCounts_eq hR.hi (fun t ht => by have := hR.hiSmall t ht; omega)
              simp only [hpp, hR.tree, e3, e4]
              refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
              refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
              refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
              have hev0 : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
              obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
              obtain ⟨g4, g5⟩ := g2 hps
              refine hnext f hf (evW - 1) cap _ _ _ _ _ _ _ _ _ floatZero _ _ _ _ (count + 1) _
                (by rw [Gen16.pred_toNat evW he]; omega) ⟨⟨f1', f2, ?_, ?_⟩, g5, g4⟩
              rotate_left
              · exact ⟨hR.lo, hR.hi, rfl, rfl, hR.loSize, hR.hiSize, hR.loSmall, hR.hiSmall⟩
              intro t ht
              by_cases hch : ∃ ch ∈ (Gen17.changesAt C n hval (Gen17.descendW c.tree P
                  (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1.toList,
                  ch.species = t
              · obtain ⟨ch, hch1, rfl⟩ := hch
                have := hsm25 ch hch1
                omega
              · push Not at hch
                have h6 := f6 t ht hch
                simp only [ite_eq_right hps] at h6
                rw [h6]; exact hrel.rel.small t ht
            · rw [ite_eq_right hsf]
              have htc : Gen19.toCache C n ⟨loW, hiW, c.tree⟩ = c := by
                simp only [Gen19.toCache, hclo', hchi', lowerOf_eq' net C hC c hrel.ok]
              have hsz := Gen16.foldRefresh_size C.gen5 codes P hP2 C.gen5.base.ms
                (Gen17.applyTest (Gen17.changesAt C n hval (Gen17.descendW c.tree P
                  (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1 n
                  (Gen17.changesAt C n hval (Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT)
                    hP2 1 Gen11.usize_one_pos (u * total) - P)).2
                  C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).pop
                (Gen17.changesAt C n hval (Gen17.descendW c.tree P
                  (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1 c
              simp only [hpp, htc, ← changesAt_val C n hval (Gen17.descendW c.tree P
                  (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)]
              rw [dite_eq_left f1'.1, dite_eq_left ⟨hsz.1.trans hlo, hsz.2.trans hhi⟩]
      · exact ih evW (prW - 1) popW ⟨loW, hiW, c.tree⟩ pop hpop c hlo hhi now total _ _ _ _ _
          count trace hev (usize_pred_toNat hpr) hrel
    · rw [dite_eq_right hT, dite_eq_right hT]
      simp only [Gen19.toCache, hcounts, hclo, hchi, lowerOf_eq' net C hC c hrel.ok]
      rw [dite_eq_left ⟨hpop, hlo, hhi⟩, Gen17.run]
      simp only [dite_eq_right hT, dite_eq_right (usize_ne_zero_of_toNat hpr)]

/-! ## The driver and the start -/

/-- Generation 19's driver returns what generation 17's returns. -/
theorem gen19_run_eq (net : Network Float) (C : Gen6.Compiled) (hC : C = Gen6.compile net)
    (codes : Array (Array Nat)) (n : Nat) (hms : C.gen5.base.ms.size = n)
    (hval : Gen15.ValidChanges C n) (P : USize) (hP2 : 2 * P.toNat < USize.size) (numRx : USize)
    (hnum : numRx.toNat = C.gen5.base.numRx) (hS : Static19 net C codes P n)
    (horizon : Float) (save : Bool) (cap : USize) :
    ∀ fuel prFuel (evW prW : USize) popW cV pop hpop c hlo hhi now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = fuel → prW.toNat = prFuel →
      Rel19 net C n popW cV pop c →
      Gen19.run C codes (Gen18.compileW C codes) C.gen5.base.ms n hms hval n.toUSize numRx P hP2
          C.gen5.base.depth.toUSize C.gen5.base.rates horizon save cap evW prW popW cV now total
          elapsed s0 s1 s2 s3 count trace =
        Gen17.run C codes C.gen5.base.ms n hms hval numRx P hP2 C.gen5.base.rates
          C.gen5.base.factors horizon save cap evW prW pop hpop c hlo hhi now total elapsed s0 s1
          s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run19_eq_of net C hC codes n hms hval P hP2 numRx hnum hS horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    refine run19_eq_of net C hC codes n hms hval P hP2 numRx hnum hS horizon save cap (f + 1) ?_
    intro f' hf' evW prW popW cV pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace hev
      hrel
    obtain rfl : f' = f := by omega
    exact ih prW.toNat evW prW popW cV pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace
      hev rfl hrel

theorem rates_of_check {rates : FloatArray}
    (h : rates.data.all (fun r => decide (floatZero ≤ r) && decide (r < Gen19.rateMax)) = true) :
    ∀ j < rates.size, decide (floatZero ≤ rates.get! j) = true ∧
      decide (rates.get! j < Float.ofNat (2 ^ 52)) = true := by
  intro j hj
  rw [Array.all_eq_true] at h
  have := h j hj
  simp only [Bool.and_eq_true] at this
  have hg : rates.get! j = rates.data[j] := by
    obtain ⟨d⟩ := rates
    exact getElem!_pos d j hj
  rw [hg]
  exact ⟨this.1, this.2⟩

theorem gen6_compile_rates (net : Network Float) :
    (Gen6.compile net).gen5.base.rates.size = (Gen6.compile net).gen5.base.numRx := by
  simp [Gen6.compile, Gen5.compile, Gen3.compile, FloatArray.size]

theorem start19_eq (net : Network Float) (hwf : ReactantsInRange net) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache)
    (hc : CacheOK net c) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) :
    Gen19.start (Gen6.compile net) (Gen13.codesOf (Gen6.compile net).gen5) horizon save cap fuel
        pop c now rng count trace =
      Gen17.start (Gen6.compile net) (Gen13.codesOf (Gen6.compile net).gen5) horizon save cap fuel
        pop c now rng count trace := by
  have hC : (Gen6.compile net).gen5.base.leaves = 2 ^ (Gen6.compile net).gen5.base.depth :=
    gen6_compile_leaves net
  have hF := gen6_compile_factors net
  have hCh := gen6_compile_changes net
  have hR := gen6_compile_rates net
  have hc' := hc
  generalize hCdef : Gen6.compile net = C at hC hF hCh hR hc' ⊢
  have hcdef : CacheOK net c := hc
  unfold Gen19.start
  by_cases hfin : Gen7.finite (c.tree.get! 1) = true
  · by_cases hpos : decide (floatZero < c.tree.get! 1) = true
    · by_cases h : 2 * C.gen5.base.leaves < USize.size
      · by_cases hs : pop.size = C.gen5.base.ms.size ∧ c.lo.size = C.gen5.base.ms.size ∧
            c.hi.size = C.gen5.base.ms.size ∧ Gen15.validChanges C C.gen5.base.ms.size = true ∧
            Gen17.changesOK C = true ∧ Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
            count + fuel < USize.size ∧ cap < USize.size ∧ C.gen5.base.numRx < USize.size ∧
            C.gen5.base.ms.size + 1 < USize.size ∧ Gen18.allSmall pop = true ∧
            Gen18.allSmall c.lo = true ∧ Gen18.allSmall c.hi = true ∧
            Gen18.allSmall C.gen5.base.ms = true ∧
            C.gen5.base.factors.all (Gen18.FactorW.ok C.gen5.base.ms.size) = true ∧
            (Gen13.codesOf C.gen5).all (·.all fun c => c == 0 || c == 1 || (c % 4 == 0 && decide (4 ≤ c) &&
              decide (c / 4 ≤ C.gen5.base.ms.size))) = true ∧
            (Gen13.codesOf C.gen5).size = C.gen5.base.ms.size ∧ C.gen5.depRates.size = C.gen5.base.ms.size ∧
            C.gen5.base.deps.size = C.gen5.base.ms.size ∧
            (List.range C.gen5.base.ms.size).all (fun s =>
              ((Gen13.codesOf C.gen5)[s]!).size == (C.gen5.base.deps[s]!).size &&
              (C.gen5.depRates[s]!).size == (C.gen5.base.deps[s]!).size &&
              decide ((C.gen5.base.deps[s]!).size < USize.size) &&
              (C.gen5.base.deps[s]!).all (· < C.gen5.base.leaves)) = true ∧
            C.changes.all (·.all fun ch => decide (ch.up < 67108864) &&
              decide (ch.down < 67108864)) = true ∧
            C.gen5.base.rates.data.all (fun r => decide (floatZero ≤ r) &&
              decide (r < Gen19.rateMax)) = true
        · simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_left h,
            dite_eq_left hs]
          have hs' := hs
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
            h18, h19, h20, h21, h22⟩ := hs'
          have hPl : C.gen5.base.leaves.toUSize.toNat = C.gen5.base.leaves :=
            toUSize_toNat_of_lt (by omega)
          have hS : Static18 C (Gen13.codesOf C.gen5) C.gen5.base.leaves.toUSize C.gen5.base.ms.size :=
            { msSmall := fun t ht => allSmall_spec h14 t ht
              nU := h10
              depth := by
                have := Nat.lt_two_pow_self (n := C.gen5.base.depth)
                omega
              leaves := hPl
              deps := depsOK_of_checks C (Gen13.codesOf C.gen5) _ _ hPl h16 h17 h20
              amounts := amounts_of_check h21
              changesSmall := validChanges_small h4
              nodup := fun j => (changesOK_spec h5 j).2
              factors := factors_of_check h15
              numFactors := hF
              numChanges := hCh }
          have hS19 : Static19 net C (Gen13.codesOf C.gen5) C.gen5.base.leaves.toUSize
              C.gen5.base.ms.size :=
            { s18 := hS
              hwf := hwf
              codes := rfl
              exclusive := fun j => (changesOK_spec h5 j).1
              rates := fun j hj => rates_of_check h22 j (by omega) }
          have hrel : Rel18 C.gen5.base.ms.size ((Gen18.toCounts pop).push 0)
              ⟨Gen18.toCounts c.lo, Gen18.toCounts c.hi, c.lower, c.tree⟩ pop c :=
            { counts := counts_push (h1 ▸ toCounts_counts pop (fun i hi => by
                have := allSmall_spec h11 i hi; omega)) 0
              size := by rw [fa_size_push, toCounts_size, h1]
              small := fun t ht => allSmall_spec h11 t (by omega)
              cache :=
                { lo := h2 ▸ toCounts_counts c.lo (fun i hi => by
                    have := allSmall_spec h12 i hi; omega)
                  hi := h3 ▸ toCounts_counts c.hi (fun i hi => by
                    have := allSmall_spec h13 i hi; omega)
                  lower := rfl
                  tree := rfl
                  loSize := by rw [toCounts_size, h2]
                  hiSize := by rw [toCounts_size, h3]
                  loSmall := fun t ht => allSmall_spec h12 t (by omega)
                  hiSmall := fun t ht => allSmall_spec h13 t (by omega) } }
          have hfu : fuel < USize.size := by omega
          rw [gen19_run_eq net C hCdef.symm (Gen13.codesOf C.gen5) C.gen5.base.ms.size rfl
            (Gen15.validChanges_spec h4) _ (Gen11.leaves_toUSize h) C.gen5.base.numRx.toUSize
            (toUSize_toNat_of_lt h9) hS19 horizon save cap.toUSize fuel cap fuel.toUSize cap.toUSize
            _ ⟨Gen18.toCounts c.lo, Gen18.toCounts c.hi, c.tree⟩ pop h1 c h2 h3 now _ floatZero
            rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize trace (toUSize_toNat_of_lt hfu)
            (toUSize_toNat_of_lt h8) ⟨hrel, hcdef, inBrackets_spec h6⟩]
          unfold Gen17.start
          simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_left h,
            dite_eq_left (show pop.size = C.gen5.base.ms.size ∧ c.lo.size = C.gen5.base.ms.size ∧
              c.hi.size = C.gen5.base.ms.size ∧
              Gen15.validChanges C C.gen5.base.ms.size = true ∧ Gen17.changesOK C = true ∧
              Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
              count + fuel < USize.size ∧ cap < USize.size ∧ C.gen5.base.numRx < USize.size from
                ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)]
        · simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_left h,
            dite_eq_right hs]
      · simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_right h]
    · simp only [Bool.not_eq_true] at hpos
      unfold Gen17.start
      simp only [hfin, hpos, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false,
        ite_true]
  · simp only [Bool.not_eq_true] at hfin
    unfold Gen17.start
    simp only [hfin, Bool.not_false, ite_true]


/-- Generation 19 returns what generation 17 returns, on every network whose reactant species are
in range and every input. -/
theorem gen19_eq_gen17 (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen19.simulate net initial start horizon rng maxEvents save cap =
      Gen17.simulate net initial start horizon rng maxEvents save cap := by
  have hinit : CacheOK net (Gen3.initialCache (Gen6.compile net).gen5.base initial) :=
    ⟨rfl, buildTree_ok _ _⟩
  unfold Gen19.simulate Gen17.simulate
  simp only [start19_eq net hwf _ _ _ _ _ _ hinit]

/-- **Generation 19 is the specification.** For every network whose reactant species are in
range and every input, generation 19 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen19_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen19.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen19_eq_gen17 net hwf, gen17_simulate_eq net hwf]

end JumpProcessesLean.Proofs
