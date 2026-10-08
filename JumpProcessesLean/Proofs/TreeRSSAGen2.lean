import JumpProcessesLean.Proofs.TreeRSSAGen1Driver
import JumpProcessesLean.TreeRSSA.Gen2

/-!
# Generation 2 is the specification, bit for bit

The inlined draws, native operations and the precomputed leaf offset compute the same
expressions as generation 1. Skipping an unchanged leaf keeps the tree of the specification's
upper bounds, because equal bit patterns are equal floats.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache fixPath descend buildTree)

/-- Equal bit patterns are equal floats. -/
theorem float_toBits_inj {a b : Float} (h : a.toBits = b.toBits) : a = b := by
  cases a with
  | ofModel ma =>
    cases b with
    | ofModel mb =>
      cases ma with
      | mk wa va =>
        cases mb with
        | mk wb vb =>
          change wa = wb at h
          subst h
          rfl

lemma array_set_self (U : Array Float) (k : Nat) (hk : k < U.size) : U.set! k U[k]! = U := by
  apply Array.ext
  · simp
  · intro i h1 h2
    by_cases hik : i = k
    · subst hik
      rw [← arr_getElem!_pos _ _ h1, ← arr_getElem!_pos _ _ h2, Array.getElem!_set!_self _ _ _ hk]
    · rw [← arr_getElem!_pos _ _ h1, ← arr_getElem!_pos _ _ h2,
        Array.getElem!_set!_ne _ _ _ _ (Ne.symm hik)]

/-! ### Bound updates with skipping -/

theorem gen2_foldl_updateBounds (net : Network Float) (lo hi : Array Nat) (ks : List Nat)
    (hks : ∀ k ∈ ks, k < net.reactions.size) :
    ∀ (lower tree : FloatArray) (U : Array Float), U.size = net.reactions.size →
      TreeOK tree U (treeDepth net.reactions.size) →
      (ks.foldl (Gen2.updateBounds (Gen2.compile net) lo hi) (lower, tree)).1.data =
          ks.foldl (fun L k => L.set! k (propensity hostArithmetic net.reactions[k]! lo)) lower.data ∧
        TreeOK (ks.foldl (Gen2.updateBounds (Gen2.compile net) lo hi) (lower, tree)).2
          (ks.foldl (fun U k => U.set! k (propensity hostArithmetic net.reactions[k]! hi)) U)
          (treeDepth net.reactions.size) := by
  have hM : net.reactions.size ≤ 2 ^ treeDepth net.reactions.size := treeDepth_spec _
  induction ks with
  | nil => intro lower tree U _ hT; exact ⟨rfl, hT⟩
  | cons k ks ih =>
    intro lower tree U hU hT
    have hk := hks k (by simp)
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
    set b := propensity hostArithmetic net.reactions[k]! hi
    have hstep : TreeOK (Gen2.updateBounds (Gen2.compile net) lo hi (lower, tree) k).2 (U.set! k b)
        (treeDepth net.reactions.size) := by
      unfold Gen2.updateBounds
      simp only
      have hnet2 : (Gen2.compile net).net = net := rfl
      have hleaves : (Gen2.compile net).leaves = 2 ^ treeDepth net.reactions.size := rfl
      have hdepth2 : (Gen2.compile net).depth = treeDepth net.reactions.size := rfl
      have hrate : Gen2.rate net.reactions[k]! hi = b := rfl
      simp only [hnet2, hleaves, hdepth2, hrate]
      split
      · rename_i hbits
        have hb : b = tree.get! (2 ^ treeDepth net.reactions.size + k) :=
          float_toBits_inj (by simpa using hbits)
        have hleaf := hT.2.1 k (by omega)
        rw [floatArray_get!_eq, hleaf, leafOf_eq, ite_eq_left (by omega)] at hb
        rw [hb, array_set_self U k (by omega)]
        exact hT
      · exact hT.update k (by omega) (by omega) b
    have := ih (fun k' hk' => hks k' (by simp [hk']))
      (lower.set! k (propensity hostArithmetic net.reactions[k]! lo))
      (Gen2.updateBounds (Gen2.compile net) lo hi (lower, tree) k).2
      (U.set! k b) (by rw [Array.size_set!, hU]) hstep
    have hfst : (Gen2.updateBounds (Gen2.compile net) lo hi (lower, tree) k).1 =
        lower.set! k (propensity hostArithmetic net.reactions[k]! lo) := rfl
    have hpair : Gen2.updateBounds (Gen2.compile net) lo hi (lower, tree) k =
        (lower.set! k (propensity hostArithmetic net.reactions[k]! lo),
          (Gen2.updateBounds (Gen2.compile net) lo hi (lower, tree) k).2) := by
      rw [← hfst]
    rw [hpair]
    simpa using this

theorem gen2_refresh_ok (net : Network Float) (hwf : ReactantsInRange net) (pop : Array Nat)
    (c : Cache) (hc : CacheOK net c) (s : Nat) :
    (Gen2.refresh (Gen2.compile net) pop c s).lo = (refreshBracket net.maxStoich (specState pop c) s).lo ∧
      (Gen2.refresh (Gen2.compile net) pop c s).hi =
        (refreshBracket net.maxStoich (specState pop c) s).hi ∧
      CacheOK net (Gen2.refresh (Gen2.compile net) pop c s) := by
  have hms : (Gen2.compile net).ms = net.maxStoich := rfl
  have hdep : (Gen2.compile net).deps = net.speciesDependents := rfl
  unfold Gen2.refresh refreshBracket
  simp only [hms, specState]
  by_cases hst : stale net.maxStoich[s]! pop[s]! c.lo[s]! c.hi[s]! = true
  · simp only [hst, ↓reduceIte]
    refine ⟨trivial, trivial, ?_⟩
    have hdeps : ∀ k ∈ net.speciesDependents[s]!.toList, k < net.reactions.size :=
      fun k hk => ((mem_speciesDependents net s k).mp hk).1
    obtain ⟨h1, h2⟩ := gen2_foldl_updateBounds net
      (c.lo.set! s (bracket net.maxStoich[s]! pop[s]!).1)
      (c.hi.set! s (bracket net.maxStoich[s]! pop[s]!).2) _ hdeps c.lower c.tree
      (net.reactions.map (propensity hostArithmetic · c.hi)) (by simp) hc.2
    simp only [← Array.foldl_toList, hdep]
    constructor
    · rw [h1, hc.1]
      exact refreshed_bounds net hwf c.lo _ s
        (fun t ht => Array.getElem!_set!_ne _ _ _ _ (Ne.symm ht))
    · have := refreshed_bounds net hwf c.hi (c.hi.set! s (bracket net.maxStoich[s]! pop[s]!).2) s
        (fun t ht => Array.getElem!_set!_ne _ _ _ _ (Ne.symm ht))
      rw [this] at h2
      exact h2
  · simp only [hst, Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, trivial, hc⟩

theorem gen2_fire_ok (net : Network Float) (hwf : ReactantsInRange net) (pop : Array Nat) (c : Cache)
    (hc : CacheOK net c) (j : Nat) :
    specState (Gen2.fire (Gen2.compile net) pop c j).1 (Gen2.fire (Gen2.compile net) pop c j).2 =
        TreeRSSA.fire net net.maxStoich (specState pop c) j ∧
      CacheOK net (Gen2.fire (Gen2.compile net) pop c j).2 := by
  unfold Gen2.fire TreeRSSA.fire
  simp only [← Array.foldl_toList]
  set pop' := (changesOf net j).toList.foldl applyChange pop
  have hnet : (Gen2.compile net).net = net := rfl
  simp only [hnet]
  have key : ∀ (l : List (Nat × Int)) (c : Cache), CacheOK net c →
      specState pop' (l.foldl (fun c ch => Gen2.refresh (Gen2.compile net) pop' c ch.1) c) =
          l.foldl (fun st ch => refreshBracket net.maxStoich st ch.1) (specState pop' c) ∧
        CacheOK net (l.foldl (fun c ch => Gen2.refresh (Gen2.compile net) pop' c ch.1) c) := by
    intro l
    induction l with
    | nil => intro c hc; exact ⟨rfl, hc⟩
    | cons ch l ih =>
      intro c hc
      obtain ⟨e1, e2, e3⟩ := gen2_refresh_ok net hwf pop' c hc ch.1
      rw [List.foldl_cons, List.foldl_cons]
      have hst : refreshBracket net.maxStoich (specState pop' c) ch.1 =
          specState pop' (Gen2.refresh (Gen2.compile net) pop' c ch.1) := by
        have hp := refreshBracket_pop net.maxStoich (specState pop' c) ch.1
        cases hr : refreshBracket net.maxStoich (specState pop' c) ch.1
        rw [hr] at e1 e2 hp
        simp only at e1 e2 hp
        simp only [specState, State.mk.injEq]
        exact ⟨hp, e1.symm, e2.symm⟩
      rw [hst]
      exact ih _ e3
  exact key (changesOf net j).toList c hc

/-! ### Proposals and events are generation 1's -/

lemma except_throw {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl

lemma except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    Except.bind (.error e) f = .error e := rfl

lemma except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    Except.bind (.ok a) f = f a := rfl

lemma except_bind_ite {ε α β : Type} (c : Prop) [Decidable c] (e : ε) (a : α)
    (f : α → Except ε β) :
    Except.bind (if c then .error e else .ok a) f = if c then .error e else f a := by
  split <;> rfl

lemma host_drawUniform (rng : Xoshiro) :
    drawUniform hostArithmetic hostSource rng =
      if (!(rng.uniform.1.isFinite && decide (floatZero ≤ rng.uniform.1) &&
          decide (rng.uniform.1 < floatOne))) = true then .error .invalidUniform
      else .ok rng.uniform := by
  have hc : (hostArithmetic.finite rng.uniform.1 && hostArithmetic.le hostArithmetic.zero rng.uniform.1 &&
      hostArithmetic.lt rng.uniform.1 hostArithmetic.one) =
      (rng.uniform.1.isFinite && decide (floatZero ≤ rng.uniform.1) &&
        decide (rng.uniform.1 < floatOne)) := rfl
  unfold drawUniform
  simp only [hostSource, bind, Except.bind, hc]
  generalize (rng.uniform.1.isFinite && decide (floatZero ≤ rng.uniform.1) &&
    decide (rng.uniform.1 < floatOne)) = b
  cases b <;> rfl

lemma host_drawExponential (rng : Xoshiro) :
    drawExponential hostArithmetic hostSource rng =
      if (!(rng.exponential.1.isFinite && decide (floatZero < rng.exponential.1))) = true then
        .error .invalidExponential
      else .ok rng.exponential := by
  have hc : (hostArithmetic.finite rng.exponential.1 &&
      hostArithmetic.lt hostArithmetic.zero rng.exponential.1) =
      (rng.exponential.1.isFinite && decide (floatZero < rng.exponential.1)) := rfl
  unfold drawExponential
  simp only [hostSource, bind, Except.bind, hc]
  generalize (rng.exponential.1.isFinite && decide (floatZero < rng.exponential.1)) = b
  cases b <;> rfl

lemma host_add (a b : Float) : hostArithmetic.add a b = a + b := rfl
lemma host_mul (a b : Float) : hostArithmetic.mul a b = a * b := rfl
lemma host_div (a b : Float) : hostArithmetic.div a b = a / b := rfl
lemma host_finite (a : Float) : hostArithmetic.finite a = a.isFinite := rfl
lemma host_lt (a b : Float) : hostArithmetic.lt a b = decide (a < b) := rfl
lemma host_le (a b : Float) : hostArithmetic.le a b = decide (a ≤ b) := rfl
lemma host_zero : hostArithmetic.zero = floatZero := rfl
lemma host_rssaAccept (l a t : Float) : rssaAccept hostArithmetic l a t = Gen2.accept l a t := rfl
lemma host_propensity (rx : Reaction Float) (pop : Array Nat) :
    propensity hostArithmetic rx pop = Gen2.rate rx pop := rfl

theorem gen2_proposals_eq (net : Network Float) (pop : Array Nat) (lower tree : FloatArray)
    (now total : Float) :
    ∀ fuel elapsed rng,
      Gen2.proposals (Gen2.compile net) pop lower tree now total fuel elapsed rng =
        Gen1.proposals (Gen1.compile net) pop lower tree now total fuel elapsed rng := by
  have h1 : (Gen1.compile net).depth = (Gen2.compile net).depth := rfl
  have h2 : 2 ^ (Gen1.compile net).depth = (Gen2.compile net).leaves := rfl
  have h3 : (Gen1.compile net).net = (Gen2.compile net).net := rfl
  have h4 : (Gen2.compile net).net.reactions.size = (Gen2.compile net).numRx := rfl
  intro fuel
  induction fuel with
  | zero => intro elapsed rng; rfl
  | succ fuel ih =>
    intro elapsed rng
    rw [Gen2.proposals, Gen1.proposals]
    simp only [bind, host_drawUniform, host_drawExponential, except_bind_ite,
      except_throw, except_bind_error, host_add, host_mul, host_div, host_finite, host_lt,
      host_rssaAccept, host_propensity, h1, h3, h4, ih, pure, Except.pure]
    rfl

theorem gen2_event_eq (net : Network Float) (pop : Array Nat) (c : Cache) (now : Float)
    (rng : Xoshiro) (cap : Nat) :
    Gen2.event (Gen2.compile net) pop c now rng cap = Gen1.event (Gen1.compile net) pop c now rng cap := by
  unfold Gen2.event Gen1.event
  simp only [gen2_proposals_eq, host_finite, host_lt, host_zero]
  rfl

theorem gen2_event_ok (net : Network Float) (pop : Array Nat) (c : Cache) (hc : CacheOK net c)
    (now : Float) (rng : Xoshiro) (cap : Nat) :
    Gen2.event (Gen2.compile net) pop c now rng cap =
      TreeRSSA.event hostArithmetic hostSource net (specState pop c) now rng cap := by
  rw [gen2_event_eq, event_ok net pop c hc]

/-! ### The driver -/

theorem gen2_loop_ok (net : Network Float) (hwf : ReactantsInRange net) (horizon : Float)
    (save : Bool) (cap : Nat) :
    ∀ fuel pop c now rng count trace, CacheOK net c →
      Gen2.loop (Gen2.compile net) horizon save cap fuel pop c now rng count trace =
        TreeRSSA.simulateLoop hostArithmetic hostSource net net.maxStoich horizon save cap fuel
          (specState pop c) now rng count trace := by
  intro fuel
  induction fuel with
  | zero =>
    intro pop c now rng count trace hc
    rw [Gen2.loop, TreeRSSA.simulateLoop, gen2_event_ok net pop c hc]
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
    rw [Gen2.loop, TreeRSSA.simulateLoop, gen2_event_ok net pop c hc]
    cases hev : TreeRSSA.event hostArithmetic hostSource net (specState pop c) now rng cap with
    | error err => rfl
    | ok p =>
      obtain ⟨ev, r⟩ := p
      cases ev with
      | none => rfl
      | some e =>
        obtain ⟨hf, hok⟩ := gen2_fire_ok net hwf pop c hc e.reaction
        simp only [bind, Except.bind, except_throw, host_le, host_finite, pure, Except.pure]
        by_cases h1 : (!decide (now ≤ e.time) || !e.time.isFinite) = true
        · simp only [h1, ↓reduceIte]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h2 : (!decide (e.time ≤ horizon)) = true
          · simp only [h2, ↓reduceIte, specState]
          · simp only [h2, Bool.false_eq_true, ↓reduceIte]
            rw [← hf, ← ih _ _ _ _ _ _ hok]

/-- **Generation 2 is the specification.** For every network whose reactant species are in
range and every input, generation 2 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen2_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen2.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save cap := by
  unfold Gen2.simulate TreeRSSA.simulate
  have hinit : CacheOK net (Gen2.initialCache (Gen2.compile net) initial) :=
    ⟨rfl, buildTree_ok _ _⟩
  have hspec : specState initial.pop (Gen2.initialCache (Gen2.compile net) initial) = initial := rfl
  simp only [bind, Except.bind, except_throw, host_le, host_lt, host_finite, pure, Except.pure]
  by_cases h1 : (!(start.isFinite && horizon.isFinite && decide (start ≤ horizon))) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (!decide (start < horizon)) = true
    · simp only [h2, ↓reduceIte]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      rw [gen2_loop_ok net hwf horizon save cap maxEvents initial.pop _ start rng 0 _ hinit, hspec]

end JumpProcessesLean.Proofs
