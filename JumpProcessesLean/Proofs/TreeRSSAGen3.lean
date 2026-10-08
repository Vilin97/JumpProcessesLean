import JumpProcessesLean.Proofs.TreeRSSAGen2
import JumpProcessesLean.TreeRSSA.Gen3

/-!
# Generation 3 is the specification, bit for bit

The compiled mass-action factors are the same natural numbers as `combinations`. Re-adding
the paths of the changed leaves of one refresh together, each path stopping where it meets
the next one, leaves every internal node the sum of its two children, so the tree is again
the flat sum tree of the specification's upper bounds.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache fixPath descend buildTree)

/-! ### Compiled mass-action factors -/

lemma fallingFactorial_one (n : Nat) : fallingFactorial n 1 = n := by
  rw [fallingFactorial, fallingFactorial]
  split <;> omega

lemma fallingFactorial_two (n : Nat) : fallingFactorial n 2 = n * (n - 1) := by
  rw [fallingFactorial, fallingFactorial_one]
  split
  · rename_i h
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> rfl
  · rfl

lemma ff_eq (n ν : Nat) (h1 : 1 ≤ ν) (h2 : ν ≤ 2) : Gen3.ff n ν = fallingFactorial n ν := by
  unfold Gen3.ff
  rcases (by omega : ν = 1 ∨ ν = 2) with rfl | rfl
  · simp [fallingFactorial_one]
  · simp [fallingFactorial_two]

theorem factor_eval_compile (rs : Array (Nat × Nat)) (pop : Array Nat) :
    (Gen3.Factor.compile rs).eval pop = combinations rs pop := by
  unfold Gen3.Factor.compile
  rw [combinations, ← Array.foldl_toList]
  split
  · rename_i s h
    rw [h]
    simp [Gen3.Factor.eval, fallingFactorial_one]
  · rename_i s h
    rw [h]
    simp [Gen3.Factor.eval, fallingFactorial_two]
  · rename_i s ν t μ h
    rw [h]
    split
    · rename_i hc
      obtain ⟨h1, h2, h3, h4⟩ := hc
      simp [Gen3.Factor.eval, ff_eq _ _ h1 h2, ff_eq _ _ h3 h4]
    · simp only [Gen3.Factor.eval, combinations, ← Array.foldl_toList, h]
  · simp only [Gen3.Factor.eval, combinations, ← Array.foldl_toList]

lemma gen3_rate_eq (net : Network Float) (k : Nat) (hk : k < net.reactions.size) (pop : Array Nat) :
    Gen3.rate (Gen3.compile net) k pop = Gen2.rate net.reactions[k]! pop := by
  unfold Gen3.rate Gen2.rate Gen3.compile
  simp only [floatArray_get!_eq]
  rw [arr_getElem!_pos _ _ (by simpa using hk), arr_getElem!_pos _ _ (by simpa using hk),
    arr_getElem!_pos _ _ hk, Array.getElem_map, Array.getElem_map, factor_eval_compile]

/-! ### Re-adding the paths of several leaves -/

/-- Re-adding the parent of `c` moves the nodes that may differ from the sum of their
children up by one level. -/
lemma h2Off_step (P : Nat) (tree : FloatArray) (c : Nat) (hs : tree.data.size = 2 * P)
    (hc : c < 2 * P) (hH : H2Off tree.data P c) :
    H2Off (tree.set! (c / 2) (tree.get! (2 * (c / 2)) + tree.get! (2 * (c / 2) + 1))).data P
      (c / 2) := by
  have hcs : c / 2 < tree.data.size := by omega
  intro k hk hkP hanc
  simp only [floatArray_set!_data, floatArray_get!_eq]
  rw [getElem!_set!_eq_ite _ _ _ _ hcs, getElem!_set!_eq_ite _ _ _ _ hcs,
    getElem!_set!_eq_ite _ _ _ _ hcs]
  by_cases hkc : k = c / 2
  · subst hkc
    simp only [ite_true, show ¬(2 * (c / 2) = c / 2) by omega,
      show ¬(2 * (c / 2) + 1 = c / 2) by omega, ite_false]
  · have h2k : ¬(2 * k = c / 2) := fun h => hanc ⟨1, by omega, by omega⟩
    have h2k1 : ¬(2 * k + 1 = c / 2) := fun h => hanc ⟨1, by omega, by omega⟩
    simp only [hkc, h2k, h2k1, ite_false]
    exact hH k hk hkP (fun ha => (strictAnc_iff c k).mp ha |>.elim hkc hanc)

lemma h2Off_zero (t : Array Float) (P c : Nat) (h : H2Off t P 0) : H2Off t P c :=
  fun k hk hkP _ => h k hk hkP (fun ⟨m, _, hm⟩ => by simp at hm; omega)

/-- Walking from `a` until its path meets the path of `b` (a node on the same level)
leaves only the strict ancestors of `b` to re-add. -/
lemma fixUntil_spec (P : Nat) : ∀ n (tree : FloatArray) a b, tree.data.size = 2 * P →
    a < 2 * P → a / 2 ^ n = b / 2 ^ n → H2Off tree.data P a →
    (Gen3.fixUntil tree n a b).data.size = 2 * P ∧
      (∀ i, P ≤ i → (Gen3.fixUntil tree n a b).data[i]! = tree.data[i]!) ∧
      H2Off (Gen3.fixUntil tree n a b).data P b := by
  intro n
  induction n with
  | zero =>
    intro tree a b hs _ hab hH
    simp only [pow_zero, Nat.div_one] at hab
    subst hab
    exact ⟨hs, fun _ _ => rfl, hH⟩
  | succ n ih =>
    intro tree a b hs ha hab hH
    simp only [Gen3.fixUntil]
    split
    · rename_i hk
      refine ⟨hs, fun _ _ => rfl, ?_⟩
      intro k hk0 hkP hanc
      apply hH k hk0 hkP
      intro ha'
      apply hanc
      rw [strictAnc_iff] at ha' ⊢
      rw [← hk]
      exact ha'
    · have hstep := h2Off_step P tree a hs ha hH
      have hs' : (tree.set! (a / 2)
          (tree.get! (2 * (a / 2)) + tree.get! (2 * (a / 2) + 1))).data.size = 2 * P := by
        simp [hs]
      have hab' : a / 2 / 2 ^ n = b / 2 / 2 ^ n := by
        rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ']
        exact hab
      obtain ⟨r1, r2, r3⟩ := ih _ (a / 2) (b / 2) hs' (by omega) hab' hstep
      refine ⟨r1, fun i hi => ?_, ?_⟩
      · rw [r2 i hi]
        simp only [floatArray_set!_data]
        rw [getElem!_set!_eq_ite _ _ _ _ (by omega)]
        simp only [show ¬(i = a / 2) by omega, ↓reduceIte]
      · intro k hk0 hkP hanc
        exact r3 k hk0 hkP (fun h => hanc ((strictAnc_iff b k).mpr (Or.inr h)))

/-- `TreeOK` except at the strict ancestors of node `c`: the tree between path updates. -/
def TreeOff (tree : FloatArray) (w : Array Float) (d c : Nat) : Prop :=
  tree.data.size = 2 * 2 ^ d ∧
    (∀ i < 2 ^ d, tree.data[2 ^ d + i]! = leafOf hostArithmetic w i) ∧
    H2Off tree.data (2 ^ d) c

lemma drop_cons_of_lt (deps : Array Nat) (i : Nat) (hi : i + 1 ≤ deps.size) :
    deps.toList.drop (deps.size - (i + 1)) =
      deps[deps.size - (i + 1)]! :: deps.toList.drop (deps.size - i) := by
  have hj : deps.size - (i + 1) < deps.toList.length := by simp; omega
  rw [List.drop_eq_getElem_cons hj, arr_getElem!_pos _ _ (by simpa using hj)]
  simp only [Array.getElem_toList]
  congr 2
  omega

theorem setBounds_spec (net : Network Float) (lo hi : Array Nat) (deps : Array Nat)
    (hdeps : ∀ k ∈ deps.toList, k < net.reactions.size) :
    ∀ i, i ≤ deps.size → ∀ (lower tree : FloatArray) (U : Array Float) (pending : Nat),
      U.size = net.reactions.size →
      (pending = 0 ∨ (2 ^ treeDepth net.reactions.size ≤ pending ∧
        pending < 2 * 2 ^ treeDepth net.reactions.size)) →
      TreeOff tree U (treeDepth net.reactions.size) pending →
      (Gen3.setBounds (Gen3.compile net) lo hi deps i lower tree pending).1.data =
          (deps.toList.drop (deps.size - i)).foldl
            (fun L k => L.set! k (propensity hostArithmetic net.reactions[k]! lo)) lower.data ∧
        TreeOK (Gen3.setBounds (Gen3.compile net) lo hi deps i lower tree pending).2
          ((deps.toList.drop (deps.size - i)).foldl
            (fun U k => U.set! k (propensity hostArithmetic net.reactions[k]! hi)) U)
          (treeDepth net.reactions.size) := by
  have hM : net.reactions.size ≤ 2 ^ treeDepth net.reactions.size := treeDepth_spec _
  have hleaves : (Gen3.compile net).leaves = 2 ^ treeDepth net.reactions.size := rfl
  have hdepth : (Gen3.compile net).depth = treeDepth net.reactions.size := rfl
  intro i
  induction i with
  | zero =>
    intro _ lower tree U pending hU hp hT
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp), List.foldl_nil, List.foldl_nil,
      Gen3.setBounds]
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
    intro hile lower tree U pending hU hp hT
    rw [drop_cons_of_lt deps i hile, List.foldl_cons, List.foldl_cons]
    have hjs : deps.size - (i + 1) < deps.size := by omega
    have hk : deps[deps.size - (i + 1)]! < net.reactions.size := by
      apply hdeps
      rw [arr_getElem!_pos _ _ hjs]
      exact Array.getElem_mem_toList hjs
    simp only [Gen3.setBounds, hleaves, hdepth]
    generalize deps[deps.size - (i + 1)]! = k at hk ⊢
    have hrate : ∀ pop, Gen3.rate (Gen3.compile net) k pop =
        propensity hostArithmetic net.reactions[k]! pop := fun pop => gen3_rate_eq net k hk pop
    simp only [hrate]
    set d := treeDepth net.reactions.size with hd
    set b := propensity hostArithmetic net.reactions[k]! hi
    set lw := propensity hostArithmetic net.reactions[k]! lo
    have hlower : (lower.set! k lw).data = lower.data.set! k lw := by simp
    by_cases hbits : (b.toBits == (tree.get! (2 ^ d + k)).toBits) = true
    · simp only [hbits, ↓reduceIte]
      have hbeq : b = tree.get! (2 ^ d + k) := float_toBits_inj (by simpa using hbits)
      have hleaf := hT.2.1 k (by omega)
      rw [floatArray_get!_eq, hleaf, leafOf_eq] at hbeq
      simp only [show k < U.size by omega, ↓reduceIte] at hbeq
      have hU' : U.set! k b = U := by rw [hbeq]; exact array_set_self U k (by omega)
      obtain ⟨r1, r2⟩ := ih (by omega) (lower.set! k lw) tree U pending hU hp hT
      rw [hU']
      rw [hlower] at r1
      exact ⟨r1, r2⟩
    · simp only [hbits, Bool.false_eq_true, ↓reduceIte]
      have hc1 : 2 ^ d + k < 2 * 2 ^ d := by omega
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
      obtain ⟨r1, r2⟩ := ih (by omega) (lower.set! k lw) _ (U.set! k b) (2 ^ d + k)
        (by simp [hU]) (Or.inr ⟨by omega, by omega⟩) hT2
      rw [hlower] at r1
      exact ⟨r1, r2⟩

/-! ### Refreshes and firings -/

theorem gen3_refresh_ok (net : Network Float) (hwf : ReactantsInRange net) (pop : Array Nat)
    (c : Cache) (hc : CacheOK net c) (s : Nat) :
    (Gen3.refresh (Gen3.compile net) pop c s).lo =
        (refreshBracket net.maxStoich (specState pop c) s).lo ∧
      (Gen3.refresh (Gen3.compile net) pop c s).hi =
        (refreshBracket net.maxStoich (specState pop c) s).hi ∧
      CacheOK net (Gen3.refresh (Gen3.compile net) pop c s) := by
  have hms : (Gen3.compile net).ms = net.maxStoich := rfl
  have hdep : (Gen3.compile net).deps = net.speciesDependents := rfl
  unfold Gen3.refresh refreshBracket
  simp only [hms, specState]
  by_cases hst : stale net.maxStoich[s]! pop[s]! c.lo[s]! c.hi[s]! = true
  · simp only [hst, ↓reduceIte, hdep]
    have hdeps : ∀ k ∈ net.speciesDependents[s]!.toList, k < net.reactions.size :=
      fun k hk => ((mem_speciesDependents net s k).mp hk).1
    obtain ⟨h1, h2⟩ := setBounds_spec net
      (c.lo.set! s (bracket net.maxStoich[s]! pop[s]!).1)
      (c.hi.set! s (bracket net.maxStoich[s]! pop[s]!).2) _ hdeps _ le_rfl c.lower c.tree
      (net.reactions.map (propensity hostArithmetic · c.hi)) 0 (by simp) (Or.inl rfl)
      ⟨hc.2.1, hc.2.2.1, fun k hk hkP _ => hc.2.2.2 k hk hkP⟩
    simp only [Nat.sub_self, List.drop_zero] at h1 h2
    refine ⟨trivial, trivial, ?_, ?_⟩
    · show (Gen3.setBounds _ _ _ _ _ _ _ _).1.data = _
      rw [h1, hc.1]
      exact refreshed_bounds net hwf c.lo _ s
        (fun t ht => Array.getElem!_set!_ne _ _ _ _ (Ne.symm ht))
    · have := refreshed_bounds net hwf c.hi (c.hi.set! s (bracket net.maxStoich[s]! pop[s]!).2) s
        (fun t ht => Array.getElem!_set!_ne _ _ _ _ (Ne.symm ht))
      rw [this] at h2
      exact h2
  · simp only [hst, Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, trivial, hc⟩

theorem gen3_fire_ok (net : Network Float) (hwf : ReactantsInRange net) (pop : Array Nat)
    (c : Cache) (hc : CacheOK net c) (j : Nat) :
    specState (Gen3.fire (Gen3.compile net) pop c j).1 (Gen3.fire (Gen3.compile net) pop c j).2 =
        TreeRSSA.fire net net.maxStoich (specState pop c) j ∧
      CacheOK net (Gen3.fire (Gen3.compile net) pop c j).2 := by
  unfold Gen3.fire TreeRSSA.fire
  simp only [← Array.foldl_toList]
  set pop' := (changesOf net j).toList.foldl applyChange pop
  have hnet : (Gen3.compile net).net = net := rfl
  simp only [hnet]
  have key : ∀ (l : List (Nat × Int)) (c : Cache), CacheOK net c →
      specState pop' (l.foldl (fun c ch => Gen3.refresh (Gen3.compile net) pop' c ch.1) c) =
          l.foldl (fun st ch => refreshBracket net.maxStoich st ch.1) (specState pop' c) ∧
        CacheOK net (l.foldl (fun c ch => Gen3.refresh (Gen3.compile net) pop' c ch.1) c) := by
    intro l
    induction l with
    | nil => intro c hc; exact ⟨rfl, hc⟩
    | cons ch l ih =>
      intro c hc
      obtain ⟨e1, e2, e3⟩ := gen3_refresh_ok net hwf pop' c hc ch.1
      rw [List.foldl_cons, List.foldl_cons]
      have hst : refreshBracket net.maxStoich (specState pop' c) ch.1 =
          specState pop' (Gen3.refresh (Gen3.compile net) pop' c ch.1) := by
        have hp := refreshBracket_pop net.maxStoich (specState pop' c) ch.1
        cases hr : refreshBracket net.maxStoich (specState pop' c) ch.1
        rw [hr] at e1 e2 hp
        simp only at e1 e2 hp
        simp only [specState, State.mk.injEq]
        exact ⟨hp, e1.symm, e2.symm⟩
      rw [hst]
      exact ih _ e3
  exact key (changesOf net j).toList c hc

/-! ### Proposals and events are generation 2's -/

lemma gen3_accept_eq (net : Network Float) (pop : Array Nat) (j : Nat) (l t : Float) :
    (decide (j < (Gen3.compile net).numRx) &&
        Gen2.accept l (Gen3.rate (Gen3.compile net) j pop) t) =
      (decide (j < (Gen2.compile net).numRx) &&
        Gen2.accept l (Gen2.rate (Gen2.compile net).net.reactions[j]! pop) t) := by
  by_cases hj : j < net.reactions.size
  · rw [gen3_rate_eq net j hj pop]
    rfl
  · have h3 : decide (j < (Gen3.compile net).numRx) = false :=
      decide_eq_false (show ¬j < (Gen3.compile net).numRx from hj)
    have h2 : decide (j < (Gen2.compile net).numRx) = false :=
      decide_eq_false (show ¬j < (Gen2.compile net).numRx from hj)
    rw [h3, h2]
    rfl

theorem gen3_proposals_eq (net : Network Float) (pop : Array Nat) (lower tree : FloatArray)
    (now total : Float) :
    ∀ fuel elapsed rng,
      Gen3.proposals (Gen3.compile net) pop lower tree now total fuel elapsed rng =
        Gen2.proposals (Gen2.compile net) pop lower tree now total fuel elapsed rng := by
  have h1 : (Gen3.compile net).depth = (Gen2.compile net).depth := rfl
  have h2 : (Gen3.compile net).leaves = (Gen2.compile net).leaves := rfl
  intro fuel
  induction fuel with
  | zero => intro elapsed rng; rfl
  | succ fuel ih =>
    intro elapsed rng
    rw [Gen3.proposals, Gen2.proposals]
    simp only [h1, h2, gen3_accept_eq, ih]

theorem gen3_event_eq (net : Network Float) (pop : Array Nat) (c : Cache) (now : Float)
    (rng : Xoshiro) (cap : Nat) :
    Gen3.event (Gen3.compile net) pop c now rng cap =
      Gen2.event (Gen2.compile net) pop c now rng cap := by
  unfold Gen3.event Gen2.event
  simp only [gen3_proposals_eq]
  rfl

theorem gen3_event_ok (net : Network Float) (pop : Array Nat) (c : Cache) (hc : CacheOK net c)
    (now : Float) (rng : Xoshiro) (cap : Nat) :
    Gen3.event (Gen3.compile net) pop c now rng cap =
      TreeRSSA.event hostArithmetic hostSource net (specState pop c) now rng cap := by
  rw [gen3_event_eq, gen2_event_ok net pop c hc]

/-! ### The driver -/

theorem gen3_loop_ok (net : Network Float) (hwf : ReactantsInRange net) (horizon : Float)
    (save : Bool) (cap : Nat) :
    ∀ fuel pop c now rng count trace, CacheOK net c →
      Gen3.loop (Gen3.compile net) horizon save cap fuel pop c now rng count trace =
        TreeRSSA.simulateLoop hostArithmetic hostSource net net.maxStoich horizon save cap fuel
          (specState pop c) now rng count trace := by
  intro fuel
  induction fuel with
  | zero =>
    intro pop c now rng count trace hc
    rw [Gen3.loop, TreeRSSA.simulateLoop, gen3_event_ok net pop c hc]
    cases hev : TreeRSSA.event hostArithmetic hostSource net (specState pop c) now rng cap with
    | error err => rfl
    | ok p =>
      obtain ⟨ev, r⟩ := p
      cases ev with
      | none => rfl
      | some e =>
        simp only [bind, Except.bind, except_throw, host_le, host_finite, pure, Except.pure]
        by_cases h1 : (!decide (now ≤ e.time) || !e.time.isFinite) = true
        · simp only [h1, ↓reduceIte]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h2 : (!decide (e.time ≤ horizon)) = true
          · simp only [h2, ↓reduceIte, specState]
          · simp only [h2, Bool.false_eq_true, ↓reduceIte]
  | succ fuel ih =>
    intro pop c now rng count trace hc
    rw [Gen3.loop, TreeRSSA.simulateLoop, gen3_event_ok net pop c hc]
    cases hev : TreeRSSA.event hostArithmetic hostSource net (specState pop c) now rng cap with
    | error err => rfl
    | ok p =>
      obtain ⟨ev, r⟩ := p
      cases ev with
      | none => rfl
      | some e =>
        obtain ⟨hf, hok⟩ := gen3_fire_ok net hwf pop c hc e.reaction
        simp only [bind, Except.bind, except_throw, host_le, host_finite, pure, Except.pure]
        by_cases h1 : (!decide (now ≤ e.time) || !e.time.isFinite) = true
        · simp only [h1, ↓reduceIte]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h2 : (!decide (e.time ≤ horizon)) = true
          · simp only [h2, ↓reduceIte, specState]
          · simp only [h2, Bool.false_eq_true, ↓reduceIte]
            rw [← hf, ← ih _ _ _ _ _ _ hok]

/-- **Generation 3 is the specification.** For every network whose reactant species are in
range and every input, generation 3 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen3_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen3.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  unfold Gen3.simulate TreeRSSA.simulate
  have hinit : CacheOK net (Gen3.initialCache (Gen3.compile net) initial) :=
    ⟨rfl, buildTree_ok _ _⟩
  have hspec : specState initial.pop (Gen3.initialCache (Gen3.compile net) initial) = initial :=
    rfl
  simp only [bind, Except.bind, except_throw, host_le, host_lt, host_finite, pure, Except.pure]
  by_cases h1 : (!(start.isFinite && horizon.isFinite && decide (start ≤ horizon))) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (!decide (start < horizon)) = true
    · simp only [h2, ↓reduceIte]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      rw [gen3_loop_ok net hwf horizon save cap maxEvents initial.pop _ start rng 0 _ hinit, hspec]

end JumpProcessesLean.Proofs
