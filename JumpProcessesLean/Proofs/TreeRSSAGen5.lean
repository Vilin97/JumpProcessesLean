import JumpProcessesLean.Proofs.TreeRSSAGen4
import JumpProcessesLean.TreeRSSA.Gen5

/-!
# Generation 5 is generation 4, hence the specification

A flat sum tree is determined by its leaves and its unused slot `0`, which no update writes.
Generation 5's refresh writes the same lower bounds and leaves as generation 3's (a skipped
bound has an unchanged integer factor, so it already holds the new value), so it returns
exactly generation 3's cache, and generation 5's driver runs exactly as generation 4's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache fixPath)

/-! ### The tree is determined by its leaves and slot `0` -/

theorem treeOK_unique {t1 t2 : FloatArray} {w : Array Float} {d : Nat} (h1 : TreeOK t1 w d)
    (h2 : TreeOK t2 w d) (h0 : t1.data[0]! = t2.data[0]!) : t1 = t2 := by
  have key : ∀ m i, 2 * 2 ^ d - m ≤ i → i < 2 * 2 ^ d → t1.data[i]! = t2.data[i]! := by
    intro m
    induction m with
    | zero => intro i hi1 hi2; omega
    | succ m ih =>
      intro i hi1 hi2
      by_cases hl : 2 ^ d ≤ i
      · have e1 := h1.2.1 (i - 2 ^ d) (by omega)
        have e2 := h2.2.1 (i - 2 ^ d) (by omega)
        rw [show 2 ^ d + (i - 2 ^ d) = i by omega] at e1 e2
        rw [e1, e2]
      · by_cases hz : i = 0
        · subst hz; exact h0
        · rw [h1.2.2 i (by omega) (by omega), h2.2.2 i (by omega) (by omega),
            ih (2 * i) (by omega) (by omega), ih (2 * i + 1) (by omega) (by omega)]
  obtain ⟨d1⟩ := t1
  obtain ⟨d2⟩ := t2
  congr 1
  apply Array.ext
  · exact h1.1.trans h2.1.symm
  · intro i hi1 hi2
    have := key (2 * 2 ^ d) i (by omega) (by have := h1.1; simp_all)
    rwa [arr_getElem!_pos _ _ hi1, arr_getElem!_pos _ _ hi2] at this

lemma fixPath_zero : ∀ n (tree : FloatArray) c, 2 ^ n ≤ c →
    (fixPath tree n c).data[0]! = tree.data[0]! := by
  intro n
  induction n with
  | zero => intro tree c _; rfl
  | succ n ih =>
    intro tree c hc
    rw [fixPath]
    have hc2 : 2 ^ n ≤ c / 2 := by
      rw [Nat.le_div_iff_mul_le (by omega)]; rw [pow_succ] at hc; exact hc
    rw [ih _ _ hc2]
    simp only [floatArray_set!_data]
    exact Array.getElem!_set!_ne _ _ _ _ (by have := Nat.one_le_two_pow (n := n); omega)

lemma fixUntil_zero : ∀ n (tree : FloatArray) a b, 2 ^ n ≤ a →
    (Gen3.fixUntil tree n a b).data[0]! = tree.data[0]! := by
  intro n
  induction n with
  | zero => intro tree a b _; rfl
  | succ n ih =>
    intro tree a b ha
    simp only [Gen3.fixUntil]
    split
    · rfl
    · have ha2 : 2 ^ n ≤ a / 2 := by
        rw [Nat.le_div_iff_mul_le (by omega)]; rw [pow_succ] at ha; exact ha
      rw [ih _ _ _ ha2]
      simp only [floatArray_set!_data]
      exact Array.getElem!_set!_ne _ _ _ _ (by have := Nat.one_le_two_pow (n := n); omega)

theorem setBounds_zero (net : Network Float) (lo hi : Array Nat) (deps : Array Nat) :
    ∀ i (lower tree : FloatArray) (pending : Nat),
      (pending = 0 ∨ 2 ^ treeDepth net.reactions.size ≤ pending) →
      (Gen3.setBounds (Gen3.compile net) lo hi deps i lower tree pending).2.data[0]! =
        tree.data[0]! := by
  have hleaves : (Gen3.compile net).leaves = 2 ^ treeDepth net.reactions.size := rfl
  have hdepth : (Gen3.compile net).depth = treeDepth net.reactions.size := rfl
  have hP : 1 ≤ 2 ^ treeDepth net.reactions.size := Nat.one_le_two_pow
  intro i
  induction i with
  | zero =>
    intro lower tree pending hp
    rw [Gen3.setBounds]
    dsimp only
    split
    · rfl
    · rename_i h0
      rw [hdepth]
      exact fixPath_zero _ _ _ (hp.resolve_left h0)
  | succ i ih =>
    intro lower tree pending hp
    simp only [Gen3.setBounds, hleaves, hdepth]
    split
    · exact ih _ _ _ hp
    · rw [ih _ _ _ (Or.inr (by omega))]
      simp only [floatArray_set!_data]
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      split
      · rfl
      · rename_i h0
        exact fixUntil_zero _ _ _ _ (hp.resolve_left h0)

/-! ### Old factors from the updated arrays -/

lemma evalAt_set (f : Gen3.Factor) (arr : Array Nat) (s v : Nat) :
    Gen5.evalAt f (arr.set! s v) s arr[s]! = f.eval arr := by
  have hget : ∀ t, (if t = s then arr[s]! else (arr.set! s v)[t]!) = arr[t]! := by
    intro t
    split
    · subst_vars; rfl
    · rename_i h; exact Array.getElem!_set!_ne _ _ _ _ (Ne.symm h)
  unfold Gen5.evalAt
  cases f with
  | one t => simp only [hget, Gen3.Factor.eval]
  | two t => simp only [hget, Gen3.Factor.eval]
  | pair t ν u μ => simp only [hget, Gen3.Factor.eval]
  | general rs => simp only [hget, Gen3.Factor.eval, combinations]

/-! ### Generation 5's bound updates -/

lemma floatArray_eq_of_data {a b : FloatArray} (h : a.data = b.data) : a = b := by
  cases a; cases b; simp_all

lemma records_factor (net : Network Float) (ks : Array Nat) (n : Nat) (hn : n < ks.size)
    (arr : Array Nat) :
    (ks.map fun k => Gen3.Factor.compile net.reactions[k]!.reactants)[n]!.eval arr =
      combinations net.reactions[ks[n]!]!.reactants arr := by
  rw [arr_getElem!_pos _ _ (by simpa using hn), Array.getElem_map, factor_eval_compile,
    arr_getElem!_pos _ _ hn]

lemma records_rate (net : Network Float) (ks : Array Nat) (n : Nat) (hn : n < ks.size) :
    (⟨ks.map fun k => net.reactions[k]!.rate⟩ : FloatArray).get! n = net.reactions[ks[n]!]!.rate := by
  rw [floatArray_get!_eq, arr_getElem!_pos _ _ (by simpa using hn), Array.getElem_map,
    arr_getElem!_pos _ _ hn]

theorem setBounds5_spec (net : Network Float) (lo0 hi0 lo1 hi1 : Array Nat) (s v w : Nat)
    (hlo : lo1 = lo0.set! s v) (hhi : hi1 = hi0.set! s w) (ks : Array Nat)
    (hks : ∀ k ∈ ks.toList, k < net.reactions.size) :
    ∀ i, i ≤ ks.size → ∀ (lower tree : FloatArray) (U : Array Float) (pending : Nat),
      lower.data.size = net.reactions.size →
      (∀ k < net.reactions.size,
        lower.data[k]! = propensity hostArithmetic net.reactions[k]! lo0 ∨
          lower.data[k]! = propensity hostArithmetic net.reactions[k]! lo1) →
      U.size = net.reactions.size →
      (∀ k < net.reactions.size, U[k]! = propensity hostArithmetic net.reactions[k]! hi0 ∨
        U[k]! = propensity hostArithmetic net.reactions[k]! hi1) →
      (pending = 0 ∨ (2 ^ treeDepth net.reactions.size ≤ pending ∧
        pending < 2 * 2 ^ treeDepth net.reactions.size)) →
      TreeOff tree U (treeDepth net.reactions.size) pending →
      (Gen5.setBounds (Gen3.compile net) lo1 hi1 s lo0[s]! hi0[s]! ks
          (ks.map fun k => Gen3.Factor.compile net.reactions[k]!.reactants)
          ⟨ks.map fun k => net.reactions[k]!.rate⟩ i lower tree pending).1.data =
          (ks.toList.drop (ks.size - i)).foldl
            (fun L k => L.set! k (propensity hostArithmetic net.reactions[k]! lo1)) lower.data ∧
        TreeOK (Gen5.setBounds (Gen3.compile net) lo1 hi1 s lo0[s]! hi0[s]! ks
            (ks.map fun k => Gen3.Factor.compile net.reactions[k]!.reactants)
            ⟨ks.map fun k => net.reactions[k]!.rate⟩ i lower tree pending).2
          ((ks.toList.drop (ks.size - i)).foldl
            (fun U k => U.set! k (propensity hostArithmetic net.reactions[k]! hi1)) U)
          (treeDepth net.reactions.size) := by
  have hM : net.reactions.size ≤ 2 ^ treeDepth net.reactions.size := treeDepth_spec _
  have hleaves : (Gen3.compile net).leaves = 2 ^ treeDepth net.reactions.size := rfl
  have hdepth : (Gen3.compile net).depth = treeDepth net.reactions.size := rfl
  intro i
  induction i with
  | zero =>
    intro _ lower tree U pending _ _ _ _ hp hT
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp), List.foldl_nil, List.foldl_nil,
      Gen5.setBounds]
    refine ⟨rfl, ?_⟩
    simp only [hdepth]
    split
    · rename_i h0
      subst h0
      exact ⟨hT.1, hT.2.1, fun k hk hkP => hT.2.2 k hk hkP
        (fun ⟨m, _, hm⟩ => by simp at hm; omega)⟩
    · rename_i h0
      have hp' := hp.resolve_left h0
      obtain ⟨hs, hl, hH⟩ := hT
      obtain ⟨r1, r2, r3⟩ := fixPath_spec (2 ^ treeDepth net.reactions.size)
        (treeDepth net.reactions.size) tree pending hs hp'.2 hH
      have hroot : pending / 2 ^ treeDepth net.reactions.size = 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [hroot] at r3
      exact ⟨r1, fun i hi => by rw [r2 _ (by omega)]; exact hl i hi,
        fun k hk hkP => r3 k hk hkP (not_strictAnc_one k hk)⟩
  | succ i ih =>
    intro hile lower tree U pending hLs hL hUs hU hp hT
    rw [drop_cons_of_lt ks i hile, List.foldl_cons, List.foldl_cons]
    have hjs : ks.size - (i + 1) < ks.size := by omega
    have hk : ks[ks.size - (i + 1)]! < net.reactions.size := by
      apply hks
      rw [arr_getElem!_pos _ _ hjs]
      exact Array.getElem_mem_toList hjs
    have hold : ∀ (f : Gen3.Factor), Gen5.evalAt f lo1 s lo0[s]! = f.eval lo0 ∧
        Gen5.evalAt f hi1 s hi0[s]! = f.eval hi0 := fun f => by
      subst hlo hhi; exact ⟨evalAt_set f lo0 s v, evalAt_set f hi0 s w⟩
    simp only [Gen5.setBounds, hleaves, hdepth, (hold _).1, (hold _).2,
      records_factor net ks _ hjs, records_rate net ks _ hjs]
    generalize ks[ks.size - (i + 1)]! = k at hk ⊢
    set d := treeDepth net.reactions.size with hd
    have hprop : ∀ arr, net.reactions[k]!.rate *
        natToFloat (combinations net.reactions[k]!.reactants arr) =
        propensity hostArithmetic net.reactions[k]! arr := fun _ => rfl
    simp only [hprop]
    -- the lower bound
    generalize hL' : (if combinations net.reactions[k]!.reactants lo1 =
        combinations net.reactions[k]!.reactants lo0 then lower
      else lower.set! k (propensity hostArithmetic net.reactions[k]! lo1)) = lower'
    have hL'd : lower'.data = lower.data.set! k (propensity hostArithmetic net.reactions[k]! lo1) := by
      rw [← hL']
      split
      · rename_i heq
        have hpe : propensity hostArithmetic net.reactions[k]! lo1 =
            propensity hostArithmetic net.reactions[k]! lo0 := by
          rw [← hprop, ← hprop, heq]
        have hcur : lower.data[k]! = propensity hostArithmetic net.reactions[k]! lo1 := by
          rcases hL k hk with h | h <;> rw [h]; exact hpe.symm
        rw [← hcur, array_set_self _ _ (by omega)]
      · simp
    have hL's : lower'.data.size = net.reactions.size := by rw [hL'd, Array.size_set!, hLs]
    have hL'v : ∀ k' < net.reactions.size,
        lower'.data[k']! = propensity hostArithmetic net.reactions[k']! lo0 ∨
          lower'.data[k']! = propensity hostArithmetic net.reactions[k']! lo1 := by
      intro k' hk'
      rw [hL'd]
      by_cases hkk : k' = k
      · subst hkk; right; exact Array.getElem!_set!_self _ _ _ (by omega)
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkk)]; exact hL k' hk'
    -- the upper bound
    by_cases hu : combinations net.reactions[k]!.reactants hi1 =
        combinations net.reactions[k]!.reactants hi0
    · simp only [hu, ↓reduceIte]
      have hpe : propensity hostArithmetic net.reactions[k]! hi1 =
          propensity hostArithmetic net.reactions[k]! hi0 := by
        rw [← hprop, ← hprop, hu]
      have hcur : U[k]! = propensity hostArithmetic net.reactions[k]! hi1 := by
        rcases hU k hk with h | h <;> rw [h]; exact hpe.symm
      have hU' : U.set! k (propensity hostArithmetic net.reactions[k]! hi1) = U := by
        rw [← hcur]; exact array_set_self U k (by omega)
      obtain ⟨r1, r2⟩ := ih (by omega) lower' tree U pending hL's hL'v hUs hU hp hT
      rw [hU', ← hL'd]
      exact ⟨r1, r2⟩
    · simp only [hu, ↓reduceIte]
      set b := propensity hostArithmetic net.reactions[k]! hi1
      have hT1 : TreeOff (if pending = 0 then tree else Gen3.fixUntil tree d pending (2 ^ d + k))
          U d (2 ^ d + k) := by
        split
        · rename_i h0
          subst h0
          exact ⟨hT.1, hT.2.1, h2Off_zero _ _ _ hT.2.2⟩
        · rename_i h0
          have hp' := hp.resolve_left h0
          obtain ⟨hs, hl, hH⟩ := hT
          have hm1 : pending / 2 ^ d = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
          have hm2 : (2 ^ d + k) / 2 ^ d = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
          have hmeet : pending / 2 ^ d = (2 ^ d + k) / 2 ^ d := by rw [hm1, hm2]
          obtain ⟨r1, r2, r3⟩ := fixUntil_spec (2 ^ d) d tree pending (2 ^ d + k) hs hp'.2 hmeet hH
          exact ⟨r1, fun i hi => by rw [r2 _ (by omega)]; exact hl i hi, r3⟩
      generalize (if pending = 0 then tree else Gen3.fixUntil tree d pending (2 ^ d + k)) = t1
        at hT1 ⊢
      have hT2 : TreeOff (t1.set! (2 ^ d + k) b) (U.set! k b) d (2 ^ d + k) := by
        obtain ⟨hs, hl, hH⟩ := hT1
        have hc : 2 ^ d + k < t1.data.size := by omega
        refine ⟨by simp [hs], fun i hi => ?_, fun k' hk' hk'P hanc => ?_⟩
        · simp only [floatArray_set!_data]
          rw [getElem!_set!_eq_ite _ _ _ _ hc, leafOf_set U k i (by omega) b, hl i hi]
          by_cases hik : i = k
          · subst hik; simp
          · simp [hik]
        · simp only [floatArray_set!_data]
          have h2k : ¬(2 * k' = 2 ^ d + k) := fun h => hanc ⟨1, by omega, by omega⟩
          have h2k1 : ¬(2 * k' + 1 = 2 ^ d + k) := fun h => hanc ⟨1, by omega, by omega⟩
          rw [getElem!_set!_eq_ite _ _ _ _ hc, getElem!_set!_eq_ite _ _ _ _ hc,
            getElem!_set!_eq_ite _ _ _ _ hc]
          simp only [show ¬(k' = 2 ^ d + k) by omega, h2k, h2k1, ↓reduceIte]
          exact hH k' hk' hk'P hanc
      have hU's : (U.set! k b).size = net.reactions.size := by simp [hUs]
      have hU'v : ∀ k' < net.reactions.size,
          (U.set! k b)[k']! = propensity hostArithmetic net.reactions[k']! hi0 ∨
            (U.set! k b)[k']! = propensity hostArithmetic net.reactions[k']! hi1 := by
        intro k' hk'
        by_cases hkk : k' = k
        · subst hkk; right; exact Array.getElem!_set!_self _ _ _ (by omega)
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkk)]; exact hU k' hk'
      obtain ⟨r1, r2⟩ := ih (by omega) lower' _ (U.set! k b) (2 ^ d + k) hL's hL'v hU's hU'v
        (Or.inr ⟨by omega, by omega⟩) hT2
      rw [← hL'd]
      exact ⟨r1, r2⟩

theorem setBounds5_zero (C : Gen3.Compiled) (hC : 1 ≤ C.leaves) (hCd : C.leaves = 2 ^ C.depth)
    (lo hi : Array Nat) (s loS hiS : Nat) (ks : Array Nat) (fs : Array Gen3.Factor)
    (rs : FloatArray) :
    ∀ i (lower tree : FloatArray) (pending : Nat), (pending = 0 ∨ 2 ^ C.depth ≤ pending) →
      (Gen5.setBounds C lo hi s loS hiS ks fs rs i lower tree pending).2.data[0]! =
        tree.data[0]! := by
  intro i
  induction i with
  | zero =>
    intro lower tree pending hp
    rw [Gen5.setBounds]
    dsimp only
    split
    · rfl
    · rename_i h0
      exact fixPath_zero _ _ _ (hp.resolve_left h0)
  | succ i ih =>
    intro lower tree pending hp
    simp only [Gen5.setBounds]
    split
    · exact ih _ _ _ hp
    · rw [ih _ _ _ (Or.inr (by omega))]
      simp only [floatArray_set!_data]
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      split
      · rfl
      · rename_i h0
        exact fixUntil_zero _ _ _ _ (hp.resolve_left h0)

/-! ### Refreshes, firings and runs are generation 3's and 4's -/

theorem gen5_refresh_eq (net : Network Float) (pop : Array Nat) (c : Cache) (hc : CacheOK net c)
    (s : Nat) :
    Gen5.refresh (Gen5.compile net) pop c s = Gen3.refresh (Gen3.compile net) pop c s := by
  have hbase : (Gen5.compile net).base = Gen3.compile net := rfl
  have hdep : (Gen3.compile net).deps = net.speciesDependents := rfl
  have hfs : (Gen5.compile net).depFactors = net.speciesDependents.map
      (·.map fun k => Gen3.Factor.compile net.reactions[k]!.reactants) := rfl
  have hrs : (Gen5.compile net).depRates = net.speciesDependents.map
      fun ks => (⟨ks.map fun k => net.reactions[k]!.rate⟩ : FloatArray) := rfl
  have hleaves : (Gen3.compile net).leaves = 2 ^ treeDepth net.reactions.size := rfl
  have hdepth : (Gen3.compile net).depth = treeDepth net.reactions.size := rfl
  have hP : 1 ≤ 2 ^ treeDepth net.reactions.size := Nat.one_le_two_pow
  unfold Gen5.refresh Gen3.refresh
  simp only [hbase]
  split
  · simp only [hdep, hfs, hrs]
    set ks := net.speciesDependents[s]!
    set lo1 := c.lo.set! s (bracket (Gen3.compile net).ms[s]! pop[s]!).1
    set hi1 := c.hi.set! s (bracket (Gen3.compile net).ms[s]! pop[s]!).2
    have hks : ∀ k ∈ ks.toList, k < net.reactions.size :=
      fun k hk => ((mem_speciesDependents net s k).mp hk).1
    have hrec : (net.speciesDependents.map
          (·.map fun k => Gen3.Factor.compile net.reactions[k]!.reactants))[s]! =
          ks.map (fun k => Gen3.Factor.compile net.reactions[k]!.reactants) ∧
        (net.speciesDependents.map
          fun ks => (⟨ks.map fun k => net.reactions[k]!.rate⟩ : FloatArray))[s]! =
          ⟨ks.map fun k => net.reactions[k]!.rate⟩ := by
      by_cases hs : s < net.speciesDependents.size
      · have e : ks = net.speciesDependents[s] := arr_getElem!_pos _ _ hs
        constructor
        · rw [arr_getElem!_pos _ _ (by simpa using hs), Array.getElem_map, e]
        · rw [arr_getElem!_pos _ _ (by simpa using hs), Array.getElem_map, e]
      · have hk0 : ks = #[] := by simp only [ks]; rw [arr_getElem!_neg _ _ hs]; rfl
        rw [hk0, arr_getElem!_neg _ _ (by simpa using hs), arr_getElem!_neg _ _ (by simpa using hs)]
        simp only [Array.map_empty]
        exact ⟨rfl, rfl⟩
    rw [hrec.1, hrec.2]
    have hU0 : ∀ k < net.reactions.size,
        (net.reactions.map (propensity hostArithmetic · c.hi))[k]! =
          propensity hostArithmetic net.reactions[k]! c.hi := by
      intro k hk
      rw [arr_getElem!_pos _ _ (by simpa using hk), Array.getElem_map, arr_getElem!_pos _ _ hk]
    have hL0 : ∀ k < net.reactions.size,
        c.lower.data[k]! = propensity hostArithmetic net.reactions[k]! c.lo := by
      intro k hk
      rw [hc.1, arr_getElem!_pos _ _ (by simpa using hk), Array.getElem_map,
        arr_getElem!_pos _ _ hk]
    obtain ⟨g1, g2⟩ := setBounds5_spec net c.lo c.hi lo1 hi1 s _ _ rfl rfl ks hks ks.size le_rfl
      c.lower c.tree (net.reactions.map (propensity hostArithmetic · c.hi)) 0
      (by rw [hc.1]; simp) (fun k hk => Or.inl (hL0 k hk)) (by simp)
      (fun k hk => Or.inl (hU0 k hk)) (Or.inl rfl)
      ⟨hc.2.1, hc.2.2.1, fun k hk hkP _ => hc.2.2.2 k hk hkP⟩
    obtain ⟨h1, h2⟩ := setBounds_spec net lo1 hi1 ks hks ks.size le_rfl c.lower c.tree
      (net.reactions.map (propensity hostArithmetic · c.hi)) 0 (by simp) (Or.inl rfl)
      ⟨hc.2.1, hc.2.2.1, fun k hk hkP _ => hc.2.2.2 k hk hkP⟩
    have z5 := setBounds5_zero (Gen3.compile net) (by rw [hleaves]; exact hP) rfl lo1 hi1 s
      c.lo[s]! c.hi[s]! ks (ks.map fun k => Gen3.Factor.compile net.reactions[k]!.reactants)
      ⟨ks.map fun k => net.reactions[k]!.rate⟩ ks.size c.lower c.tree 0 (Or.inl rfl)
    have z3 := setBounds_zero net lo1 hi1 ks ks.size c.lower c.tree 0 (Or.inl rfl)
    congr 1
    · exact floatArray_eq_of_data (g1.trans h1.symm)
    · exact treeOK_unique g2 h2 (z5.trans z3.symm)
  · rfl

theorem gen5_fire_eq (net : Network Float) (hwf : ReactantsInRange net) (pop : Array Nat)
    (c : Cache) (hc : CacheOK net c) (j : Nat) :
    Gen5.fire (Gen5.compile net) pop c j = Gen3.fire (Gen3.compile net) pop c j := by
  unfold Gen5.fire Gen3.fire
  have hnet : (Gen5.compile net).base.net = (Gen3.compile net).net := rfl
  rw [hnet]
  simp only [← Array.foldl_toList]
  congr 1
  generalize (changesOf (Gen3.compile net).net j).toList = l
  generalize (l.foldl applyChange pop) = pop'
  induction l generalizing c with
  | nil => rfl
  | cons ch l ih =>
    rw [List.foldl_cons, List.foldl_cons, gen5_refresh_eq net pop' c hc ch.1]
    exact ih _ (gen3_refresh_ok net hwf pop' c hc ch.1).2.2

lemma gen5_compile_base (net : Network Float) : (Gen5.compile net).base = Gen3.compile net := rfl

/-- Generation 5's driver from one proposal on is generation 4's when the two firings agree
on caches satisfying an invariant that firing preserves, given the statement for the next
event. -/
theorem run5_eq_of (C : Gen5.Compiled) (Inv : Cache → Prop)
    (hfire : ∀ pop c j, Inv c → Gen5.fire C pop c j = Gen4.fire C.base pop c j)
    (hinv : ∀ pop c j, Inv c → Inv (Gen4.fire C.base pop c j).2)
    (horizon : Float) (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Inv c →
      Gen5.run C horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen4.run C.base horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace, Inv c →
      Gen5.run C horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen4.run C.base horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count
          trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace _
    rw [Gen5.run.eq_1, Gen4.run.eq_1]
  | succ pf ih =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace hc
    rw [Gen5.run.eq_2, Gen4.run.eq_2]
    rcases h1 : Xoshiro.uniform ⟨s0, s1, s2, s3⟩ with ⟨u, r1⟩
    dsimp only
    by_cases hu : (!(u.isFinite && decide (floatZero ≤ u) && decide (u < floatOne))) = true
    · simp only [hu, ↓reduceIte]
    simp only [hu, Bool.false_eq_true, ↓reduceIte]
    rcases h2 : r1.exponential with ⟨e, r2⟩
    dsimp only
    by_cases he : (!(e.isFinite && decide (floatZero < e))) = true
    · simp only [he, ↓reduceIte]
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    by_cases hel : (!(elapsed + e).isFinite) = true
    · simp only [hel, ↓reduceIte]
    simp only [hel, Bool.false_eq_true, ↓reduceIte]
    rcases h3 : r2.uniform with ⟨v, r3⟩
    dsimp only
    by_cases hv : (!(v.isFinite && decide (floatZero ≤ v) && decide (v < floatOne))) = true
    · simp only [hv, ↓reduceIte]
    simp only [hv, Bool.false_eq_true, ↓reduceIte]
    generalize Gen1.descend c.tree C.base.depth 1 (u * total) - C.base.leaves = j
    by_cases hacc : (decide (j < C.base.numRx) &&
        Gen2.accept (c.lower.get! j) (Gen3.rate C.base j pop)
          (v * c.tree.get! (C.base.leaves + j))) = true
    · simp only [hacc, ↓reduceIte]
      generalize now + (elapsed + e) / total = time
      by_cases ht : (!(time.isFinite && decide (now < time))) = true
      · simp only [ht, ↓reduceIte]
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      by_cases hle : (!decide (now ≤ time)) = true
      · simp only [hle, ↓reduceIte]
      simp only [hle, Bool.false_eq_true, ↓reduceIte]
      by_cases hh : (!decide (time ≤ horizon)) = true
      · simp only [hh, ↓reduceIte]
      simp only [hh, Bool.false_eq_true, ↓reduceIte]
      cases fuel with
      | zero => rfl
      | succ f =>
        dsimp only
        rw [hfire pop c j hc]
        have hc' := hinv pop c j hc
        rcases hf : Gen4.fire C.base pop c j with ⟨pop', c'⟩
        rw [hf] at hc'
        dsimp only
        by_cases hfin' : (!(c'.tree.get! 1).isFinite) = true
        · simp only [hfin', ↓reduceIte]
        simp only [hfin', Bool.false_eq_true, ↓reduceIte]
        by_cases hpos : (!decide (floatZero < c'.tree.get! 1)) = true
        · simp only [hpos, ↓reduceIte]
        simp only [hpos, Bool.false_eq_true, ↓reduceIte]
        rw [hnext f rfl _ _ _ _ _ _ _ _ _ _ _ _ hc']
    · simp only [hacc, Bool.false_eq_true, ↓reduceIte]
      rw [ih _ _ _ _ _ _ _ _ _ _ _ hc]

theorem gen5_run_eq (net : Network Float) (hwf : ReactantsInRange net) (horizon : Float)
    (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace, CacheOK net c →
      Gen5.run (Gen5.compile net) horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2
          s3 count trace =
        Gen4.run (Gen3.compile net) horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2
          s3 count trace := by
  have hfire : ∀ pop c j, CacheOK net c →
      Gen5.fire (Gen5.compile net) pop c j = Gen4.fire (Gen5.compile net).base pop c j :=
    fun pop c j hc => gen5_fire_eq net hwf pop c hc j
  have hinv : ∀ pop c j, CacheOK net c → CacheOK net (Gen4.fire (Gen5.compile net).base pop c j).2 :=
    fun pop c j hc => (gen3_fire_ok net hwf pop c hc j).2
  intro fuel
  induction fuel with
  | zero =>
    exact run5_eq_of _ _ hfire hinv horizon save cap 0 (fun f h => absurd h (by omega))
  | succ f ih =>
    exact run5_eq_of _ _ hfire hinv horizon save cap (f + 1) (fun f' h => by cases h; exact ih)

theorem gen5_start_eq (net : Network Float) (hwf : ReactantsInRange net) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (hc : CacheOK net c)
    (now : Float) (rng : Xoshiro) (count : Nat) (trace : Array (Float × State)) :
    Gen5.start (Gen5.compile net) horizon save cap fuel pop c now rng count trace =
      Gen4.start (Gen3.compile net) horizon save cap fuel pop c now rng count trace := by
  unfold Gen5.start Gen4.start
  simp only [gen5_compile_base]
  by_cases h1 : (!(c.tree.get! 1).isFinite) = true
  · simp only [h1, ↓reduceIte]
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : (!decide (floatZero < c.tree.get! 1)) = true
  · simp only [h2, ↓reduceIte]
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  rw [gen5_run_eq net hwf horizon save cap _ _ _ _ _ _ _ _ _ _ _ _ _ hc]

/-- Generation 5 returns what generation 4 returns, on every network whose reactant species
are in range. -/
theorem gen5_eq_gen4 (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen5.simulate net initial start horizon rng maxEvents save cap =
      Gen4.simulate net initial start horizon rng maxEvents save cap := by
  have hinit : CacheOK net (Gen3.initialCache (Gen3.compile net) initial) :=
    ⟨rfl, buildTree_ok _ _⟩
  unfold Gen5.simulate Gen4.simulate
  simp only [gen5_compile_base, gen5_start_eq net hwf _ _ _ _ _ _ hinit]

/-- **Generation 5 is the specification.** For every network whose reactant species are in
range and every input, generation 5 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen5_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen5.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen5_eq_gen4 net hwf, gen4_simulate_eq net hwf]

end JumpProcessesLean.Proofs
