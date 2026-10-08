import JumpProcessesLean.Proofs.TreeRSSAFlatTree
import JumpProcessesLean.Proofs.TreeRSSAModel

/-!
# Generation 1 is the specification, bit for bit

`Gen1.simulate net` returns exactly `TreeRSSA.simulate hostArithmetic hostSource net` for
every input: same draws, proposals, acceptances, times, errors, states and trace. The
proof keeps the cache invariant `CacheOK`: the cached lower bounds are the specification's
lower bounds and the flat tree is the specification's tree of upper bounds. Only bounds of
reactions that use a refreshed species change, and the dependency lists contain all of
them.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1

/-! ### Dependency lists -/

lemma addDependent_size (j : Nat) (deps : Array (Array Nat)) (p : Nat × Nat) :
    (Network.addDependent j deps p).size = deps.size := by
  unfold Network.addDependent; split <;> simp

lemma arr_getElem!_pos {β : Type} [Inhabited β] (a : Array β) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] := getElem!_pos a i h

lemma arr_getElem!_neg {β : Type} [Inhabited β] (a : Array β) (i : Nat) (h : ¬i < a.size) :
    a[i]! = default := getElem!_neg a i h

lemma addDependent_get (j : Nat) (deps : Array (Array Nat)) (p : Nat × Nat) (t : Nat) :
    (Network.addDependent j deps p)[t]! =
      if t = p.1 ∧ p.1 < deps.size then deps[t]!.push j else deps[t]! := by
  unfold Network.addDependent
  split
  · rename_i hp
    by_cases ht : t = p.1
    · subst ht
      rw [ite_eq_left ⟨rfl, hp⟩, arr_getElem!_pos _ _ (by simpa using hp), Array.getElem_modify,
        ite_eq_left rfl, arr_getElem!_pos _ _ hp]
    · rw [ite_eq_right (fun h => ht h.1)]
      by_cases hts : t < deps.size
      · rw [arr_getElem!_pos _ _ (by simpa using hts), Array.getElem_modify, ite_eq_right (Ne.symm ht),
          arr_getElem!_pos _ _ hts]
      · rw [arr_getElem!_neg _ _ (by simpa using hts), arr_getElem!_neg _ _ hts]
  · rename_i hp
    rw [ite_eq_right (fun h => hp h.2)]

/-- Every listed dependent is the reaction being recorded or was listed before. -/
lemma addDependent_mem (j : Nat) (deps : Array (Array Nat)) (p : Nat × Nat) (t x : Nat) :
    x ∈ (Network.addDependent j deps p)[t]!.toList ↔
      x ∈ deps[t]!.toList ∨ (t = p.1 ∧ p.1 < deps.size ∧ x = j) := by
  rw [addDependent_get]
  split
  · rename_i h; simp [h.1, h.2, or_comm]
  · rename_i h
    simp only [iff_self_or, and_imp]
    intro ht hp
    exact absurd ⟨ht, hp⟩ h

private def depStep {α : Type} (net : Network α) (deps : Array (Array Nat)) (j : Nat) :
    Array (Array Nat) :=
  match net.reactions[j]? with
  | some rx => rx.reactants.foldl (Network.addDependent j) deps
  | none => deps

private lemma speciesDependents_eq {α : Type} (net : Network α) :
    net.speciesDependents = (List.range net.reactions.size).foldl (depStep net)
      (Array.replicate net.numSpecies #[]) := rfl

private lemma inner_size (j : Nat) (l : List (Nat × Nat)) (deps : Array (Array Nat)) :
    (l.foldl (Network.addDependent j) deps).size = deps.size := by
  induction l generalizing deps with
  | nil => rfl
  | cons p l ih => rw [List.foldl_cons, ih, addDependent_size]

private lemma inner_mem (j : Nat) (l : List (Nat × Nat)) (deps : Array (Array Nat)) (t x : Nat) :
    x ∈ (l.foldl (Network.addDependent j) deps)[t]!.toList ↔
      x ∈ deps[t]!.toList ∨ (x = j ∧ t < deps.size ∧ ∃ p ∈ l, p.1 = t) := by
  induction l generalizing deps with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih, addDependent_mem, addDependent_size]
    constructor
    · rintro ((h | ⟨rfl, hs, rfl⟩) | ⟨rfl, hs, q, hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, hs, p, by simp, rfl⟩
      · exact Or.inr ⟨rfl, hs, q, by simp [hq], rfl⟩
    · rintro (h | ⟨rfl, hs, q, hq, rfl⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl (Or.inr ⟨rfl, hs, rfl⟩)
        · exact Or.inr ⟨rfl, hs, q, hq, rfl⟩

private lemma depStep_size {α : Type} (net : Network α) (deps : Array (Array Nat)) (j : Nat) :
    (depStep net deps j).size = deps.size := by
  unfold depStep
  split
  · rw [← Array.foldl_toList, inner_size]
  · rfl

private lemma depStep_mem {α : Type} (net : Network α) (deps : Array (Array Nat)) (j t x : Nat) :
    x ∈ (depStep net deps j)[t]!.toList ↔
      x ∈ deps[t]!.toList ∨ (x = j ∧ t < deps.size ∧
        ∃ rx, net.reactions[j]? = some rx ∧ ∃ p ∈ rx.reactants.toList, p.1 = t) := by
  unfold depStep
  split
  · rename_i rx hrx
    rw [← Array.foldl_toList, inner_mem]
    simp [hrx]
  · rename_i hrx
    simp [hrx]

private lemma outer_mem {α : Type} (net : Network α) (js : List Nat) (deps : Array (Array Nat))
    (t x : Nat) :
    x ∈ (js.foldl (depStep net) deps)[t]!.toList ↔
      x ∈ deps[t]!.toList ∨ (x ∈ js ∧ t < deps.size ∧
        ∃ rx, net.reactions[x]? = some rx ∧ ∃ p ∈ rx.reactants.toList, p.1 = t) := by
  induction js generalizing deps with
  | nil => simp
  | cons j js ih =>
    rw [List.foldl_cons, ih, depStep_mem, depStep_size]
    constructor
    · rintro ((h | ⟨rfl, hs, rest⟩) | ⟨hx, hs, rest⟩)
      · exact Or.inl h
      · exact Or.inr ⟨by simp, hs, rest⟩
      · exact Or.inr ⟨by simp [hx], hs, rest⟩
    · rintro (h | ⟨hx, hs, rest⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl (Or.inr ⟨rfl, hs, rest⟩)
        · exact Or.inr ⟨hx, hs, rest⟩

/-- The dependents of a species are exactly the reactions that use it as a reactant. -/
theorem mem_speciesDependents {α : Type} (net : Network α) (s x : Nat) :
    x ∈ net.speciesDependents[s]!.toList ↔
      x < net.reactions.size ∧ s < net.numSpecies ∧
        ∃ p ∈ (net.reactions[x]?.map (·.reactants.toList)).getD [], p.1 = s := by
  rw [speciesDependents_eq, outer_mem]
  have hrep : ∀ t : Nat, (Array.replicate net.numSpecies (#[] : Array Nat))[t]! = #[] := by
    intro t
    by_cases ht : t < net.numSpecies
    · rw [arr_getElem!_pos _ _ (by simpa using ht)]; simp
    · rw [arr_getElem!_neg _ _ (by simpa using ht)]; rfl
  simp only [hrep, Array.toList_empty, List.not_mem_nil, false_or, List.mem_range,
    Array.size_replicate]
  constructor
  · rintro ⟨hx, hs, rx, hrx, p, hp, rfl⟩
    exact ⟨hx, hs, p, by simp [hrx, hp], rfl⟩
  · rintro ⟨hx, hs, p, hp, rfl⟩
    obtain ⟨rx, hrx⟩ : ∃ rx, net.reactions[x]? = some rx := ⟨net.reactions[x], by simp [hx]⟩
    exact ⟨hx, hs, rx, hrx, p, by simpa [hrx] using hp, rfl⟩

/-! ### Bound updates -/

lemma foldl_set_size (f : Nat → Float) (ks : List Nat) (L : Array Float) :
    (ks.foldl (fun L k => L.set! k (f k)) L).size = L.size := by
  induction ks generalizing L with
  | nil => rfl
  | cons k ks ih => rw [List.foldl_cons, ih, Array.size_set!]

lemma foldl_set_get (f : Nat → Float) (ks : List Nat) (L : Array Float) (j : Nat) :
    (ks.foldl (fun L k => L.set! k (f k)) L)[j]! =
      if j ∈ ks ∧ j < L.size then f j else L[j]! := by
  induction ks generalizing L with
  | nil => simp
  | cons k ks ih =>
    rw [List.foldl_cons, ih, Array.size_set!]
    by_cases hj : j < L.size
    · by_cases hk : j = k
      · subst hk
        simp [hj]
      · by_cases hmem : j ∈ ks
        · simp [hmem, hj]
        · have h1 : ¬(j ∈ ks ∧ j < L.size) := fun h => hmem h.1
          have h2 : ¬(j ∈ k :: ks ∧ j < L.size) := by simp [hmem, hk]
          rw [ite_eq_right h1, ite_eq_right h2, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk)]
    · have hn : (L.set! k (f k))[j]! = L[j]! := by
        rw [arr_getElem!_neg _ _ (by simpa using hj), arr_getElem!_neg _ _ hj]
      simp [hj]

lemma combinations_congr (rs : Array (Nat × Nat)) (pop pop' : Array Nat)
    (h : ∀ p ∈ rs.toList, pop[p.1]! = pop'[p.1]!) :
    combinations rs pop = combinations rs pop' := by
  rw [combinations_eq, combinations_eq]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [h p hp]

/-- Re-evaluating the dependents of `s` after changing only entry `s` recomputes the map. -/
theorem refreshed_bounds (net : Network Float)
    (hwf : ∀ rx ∈ net.reactions.toList, ∀ p ∈ rx.reactants.toList, p.1 < net.numSpecies)
    (lo lo' : Array Nat) (s : Nat) (hagree : ∀ t, t ≠ s → lo'[t]! = lo[t]!) :
    (net.speciesDependents[s]!.toList.foldl
        (fun L k => L.set! k (propensity hostArithmetic net.reactions[k]! lo'))
        (net.reactions.map (propensity hostArithmetic · lo))) =
      net.reactions.map (propensity hostArithmetic · lo') := by
  apply Array.ext
  · rw [foldl_set_size]; simp
  · intro j h1 h2
    have hj : j < net.reactions.size := by simpa using h2
    have hget := foldl_set_get (fun k => propensity hostArithmetic net.reactions[k]! lo')
      net.speciesDependents[s]!.toList (net.reactions.map (propensity hostArithmetic · lo)) j
    rw [arr_getElem!_pos _ _ h1] at hget
    rw [hget]
    simp only [Array.size_map, hj, and_true, Array.getElem_map]
    split
    · rw [getElem!_pos net.reactions j hj]
    · rename_i hmem
      rw [arr_getElem!_pos _ _ (by simpa using hj), Array.getElem_map]
      unfold propensity
      rw [combinations_congr _ lo lo']
      intro p hp
      have hps : p.1 ≠ s := by
        intro hps
        apply hmem
        rw [mem_speciesDependents]
        refine ⟨hj, ?_, p, by simp [hj, hp], hps⟩
        rw [← hps]
        exact hwf _ (Array.getElem_mem_toList _) p hp
      exact (hagree _ hps).symm

/-- Folding `updateBounds` over in-range reactions updates the arrays it represents. -/
theorem foldl_updateBounds (C : Compiled) (lo hi : Array Nat) (ks : List Nat)
    (hks : ∀ k ∈ ks, k < C.net.reactions.size) (hM : C.net.reactions.size ≤ 2 ^ C.depth) :
    ∀ (lower tree : FloatArray) (U : Array Float), U.size = C.net.reactions.size →
      TreeOK tree U C.depth →
      (ks.foldl (updateBounds C lo hi) (lower, tree)).1.data =
          ks.foldl (fun L k => L.set! k (propensity hostArithmetic C.net.reactions[k]! lo))
            lower.data ∧
        TreeOK (ks.foldl (updateBounds C lo hi) (lower, tree)).2
          (ks.foldl (fun U k => U.set! k (propensity hostArithmetic C.net.reactions[k]! hi)) U)
          C.depth := by
  induction ks with
  | nil => intro lower tree U _ hT; exact ⟨rfl, hT⟩
  | cons k ks ih =>
    intro lower tree U hU hT
    have hk := hks k (by simp)
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
    have hT' := hT.update k (by omega) (by omega) (propensity hostArithmetic C.net.reactions[k]! hi)
    have := ih (fun k' hk' => hks k' (by simp [hk']))
      (lower.set! k (propensity hostArithmetic C.net.reactions[k]! lo))
      (fixPath (tree.set! (2 ^ C.depth + k) (propensity hostArithmetic C.net.reactions[k]! hi)) C.depth
        (2 ^ C.depth + k))
      (U.set! k (propensity hostArithmetic C.net.reactions[k]! hi)) (by rw [Array.size_set!, hU]) hT'
    simpa [updateBounds] using this

/-! ### The cache invariant -/

/-- The cached lower bounds and the flat tree are the specification's bounds and tree. -/
def CacheOK (net : Network Float) (c : Cache) : Prop :=
  c.lower.data = net.reactions.map (propensity hostArithmetic · c.lo) ∧
    TreeOK c.tree (net.reactions.map (propensity hostArithmetic · c.hi)) (treeDepth net.reactions.size)

/-- The specification state represented by populations and a cache. -/
abbrev specState (pop : Array Nat) (c : Cache) : State := ⟨pop, c.lo, c.hi⟩

/-- Reactant species are in range. -/
def ReactantsInRange (net : Network Float) : Prop :=
  ∀ rx ∈ net.reactions.toList, ∀ p ∈ rx.reactants.toList, p.1 < net.numSpecies

theorem refresh_ok (net : Network Float) (hwf : ReactantsInRange net) (pop : Array Nat) (c : Cache)
    (hc : CacheOK net c) (s : Nat) :
    (refresh (compile net) pop c s).lo = (refreshBracket net.maxStoich (specState pop c) s).lo ∧
      (refresh (compile net) pop c s).hi = (refreshBracket net.maxStoich (specState pop c) s).hi ∧
      CacheOK net (refresh (compile net) pop c s) := by
  have hms : (compile net).ms = net.maxStoich := rfl
  have hnet : (compile net).net = net := rfl
  have hdep : (compile net).deps = net.speciesDependents := rfl
  have hdepth : (compile net).depth = treeDepth net.reactions.size := rfl
  unfold refresh refreshBracket
  simp only [hms, specState]
  by_cases hst : stale net.maxStoich[s]! pop[s]! c.lo[s]! c.hi[s]! = true
  · simp only [hst, ↓reduceIte]
    refine ⟨trivial, trivial, ?_⟩
    have hdeps : ∀ k ∈ (compile net).deps[s]!.toList, k < (compile net).net.reactions.size :=
      fun k hk => ((mem_speciesDependents net s k).mp hk).1
    have hM : (compile net).net.reactions.size ≤ 2 ^ (compile net).depth := treeDepth_spec _
    obtain ⟨h1, h2⟩ := foldl_updateBounds (compile net)
      (c.lo.set! s (bracket net.maxStoich[s]! pop[s]!).1)
      (c.hi.set! s (bracket net.maxStoich[s]! pop[s]!).2) _ hdeps hM c.lower c.tree
      (net.reactions.map (propensity hostArithmetic · c.hi)) (by simp; rfl) hc.2
    simp only [← Array.foldl_toList]
    simp only [hnet, hdep, hdepth] at h1 h2 ⊢
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

theorem fire_ok (net : Network Float) (hwf : ReactantsInRange net) (pop : Array Nat) (c : Cache)
    (hc : CacheOK net c) (j : Nat) :
    (Gen1.fire (compile net) pop c j).1 = (TreeRSSA.fire net net.maxStoich (specState pop c) j).pop ∧
      (Gen1.fire (compile net) pop c j).2.lo = (TreeRSSA.fire net net.maxStoich (specState pop c) j).lo ∧
      (Gen1.fire (compile net) pop c j).2.hi = (TreeRSSA.fire net net.maxStoich (specState pop c) j).hi ∧
      CacheOK net (Gen1.fire (compile net) pop c j).2 := by
  unfold Gen1.fire TreeRSSA.fire
  simp only [← Array.foldl_toList]
  set pop' := (changesOf net j).toList.foldl applyChange pop
  have key : ∀ (l : List (Nat × Int)) (c : Cache), CacheOK net c →
      (l.foldl (fun c ch => refresh (compile net) pop' c ch.1) c).lo =
          (l.foldl (fun st ch => refreshBracket net.maxStoich st ch.1) (specState pop' c)).lo ∧
        (l.foldl (fun c ch => refresh (compile net) pop' c ch.1) c).hi =
          (l.foldl (fun st ch => refreshBracket net.maxStoich st ch.1) (specState pop' c)).hi ∧
        (l.foldl (fun st ch => refreshBracket net.maxStoich st ch.1) (specState pop' c)).pop = pop' ∧
        CacheOK net (l.foldl (fun c ch => refresh (compile net) pop' c ch.1) c) := by
    intro l
    induction l with
    | nil => intro c hc; exact ⟨rfl, rfl, rfl, hc⟩
    | cons ch l ih =>
      intro c hc
      obtain ⟨e1, e2, e3⟩ := refresh_ok net hwf pop' c hc ch.1
      rw [List.foldl_cons, List.foldl_cons]
      have hst : refreshBracket net.maxStoich (specState pop' c) ch.1 =
          specState pop' (refresh (compile net) pop' c ch.1) := by
        have hp := refreshBracket_pop net.maxStoich (specState pop' c) ch.1
        cases hr : refreshBracket net.maxStoich (specState pop' c) ch.1
        rw [hr] at e1 e2 hp
        simp only at e1 e2 hp
        simp only [specState, State.mk.injEq]
        exact ⟨hp, e1.symm, e2.symm⟩
      rw [hst]
      exact ih _ e3
  obtain ⟨k1, k2, k3, k4⟩ := key (changesOf net j).toList c hc
  exact ⟨k3.symm, k1, k2, k4⟩

/-! ### Events and the driver -/

lemma hostArith_finite (a : Float) : hostArithmetic.finite a = a.isFinite := rfl
lemma hostArith_le (a b : Float) : hostArithmetic.le a b = decide (a ≤ b) := rfl
lemma hostArith_lt' (a b : Float) : hostArithmetic.lt a b = decide (a < b) := rfl

theorem proposals_ok (net : Network Float) (pop lo hi : Array Nat) (lower tree : FloatArray)
    (hl : lower.data = net.reactions.map (propensity hostArithmetic · lo))
    (ht : TreeOK tree (net.reactions.map (propensity hostArithmetic · hi)) (treeDepth net.reactions.size))
    (now total : Float) :
    ∀ fuel elapsed rng,
      Gen1.proposals (compile net) pop lower tree now total fuel elapsed rng =
        TreeRSSA.proposals hostArithmetic hostSource net pop
          (net.reactions.map (propensity hostArithmetic · lo))
          (net.reactions.map (propensity hostArithmetic · hi)) (treeDepth net.reactions.size) now total
          fuel elapsed rng := by
  have hnet : (compile net).net = net := rfl
  have hdepth : (compile net).depth = treeDepth net.reactions.size := rfl
  set d := treeDepth net.reactions.size
  have hM : net.reactions.size ≤ 2 ^ d := treeDepth_spec _
  have hdesc : ∀ x, Gen1.descend tree d 1 x - 2 ^ d =
      segDescend hostArithmetic (net.reactions.map (propensity hostArithmetic · hi)) d 0 x := by
    intro x
    rw [ht.descend d 1 x (by simp) (by simp)]
    simp
  intro fuel
  induction fuel with
  | zero => intro elapsed rng; rfl
  | succ fuel ih =>
    intro elapsed rng
    rw [Gen1.proposals, TreeRSSA.proposals]
    simp only [hnet, hdepth]
    cases hU : drawUniform hostArithmetic hostSource rng with
    | error e => simp [bind, Except.bind]
    | ok p =>
      obtain ⟨u, rng1⟩ := p
      simp only [bind, Except.bind]
      rw [hdesc]
      set j := segDescend hostArithmetic (net.reactions.map (propensity hostArithmetic · hi)) d 0
        (hostArithmetic.mul u total)
      have hacc : ∀ v : Float,
          (decide (j < net.reactions.size) && rssaAccept hostArithmetic (lower.get! j)
            (propensity hostArithmetic net.reactions[j]! pop)
              (hostArithmetic.mul v (tree.get! (2 ^ d + j)))) =
          (decide (j < net.reactions.size) && rssaAccept hostArithmetic
            (net.reactions.map (propensity hostArithmetic · lo))[j]!
            (propensity hostArithmetic net.reactions[j]! pop)
            (hostArithmetic.mul v (net.reactions.map (propensity hostArithmetic · hi))[j]!)) := by
        intro v
        by_cases hj : j < net.reactions.size
        · have hleaf := ht.2.1 j (by omega)
          rw [floatArray_get!_eq, floatArray_get!_eq, hleaf, hl, leafOf_eq]
          simp only [Array.size_map, hj, ↓reduceIte]
        · simp [hj]
      simp only [hacc, ih]

theorem event_ok (net : Network Float) (pop : Array Nat) (c : Cache) (hc : CacheOK net c)
    (now : Float) (rng : Xoshiro) (cap : Nat) :
    Gen1.event (compile net) pop c now rng cap =
      TreeRSSA.event hostArithmetic hostSource net (specState pop c) now rng cap := by
  have hnet : (compile net).net = net := rfl
  unfold Gen1.event TreeRSSA.event
  rw [hc.2.root]
  simp only [hnet, TreeRSSA.lowerBounds, TreeRSSA.upperBounds]
  rw [proposals_ok net pop c.lo c.hi c.lower c.tree hc.1 hc.2]
  rfl

end JumpProcessesLean.Proofs
