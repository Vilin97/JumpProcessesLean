import JumpProcessesLean.Proofs.TreeRSSAGen26
import JumpProcessesLean.TreeRSSA.Gen27

/-!
# Generation 27 is generation 26, hence the specification

Generation 27 runs generation 26's driver on the same inputs, built with less work: its compile
is `Gen6.compile` (`compile27_eq`: `factorOf` is `Gen3.Factor.compile`, and each dependent's
factor is its reaction's), its initial tree is `Gen1.buildTree`'s (`initialTree_eq`), and the
lower bounds left out of its initial cache are read only by the fallback, which computes them
(`start27_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

/-- `factorOf` is `Gen3.Factor.compile`. -/
theorem factorOf_eq (rs : Array (Nat × Nat)) : Gen27.factorOf rs = Gen3.Factor.compile rs := by
  obtain ⟨l⟩ := rs
  unfold Gen27.factorOf Gen3.Factor.compile
  match l with
  | [] => simp
  | [(s, ν)] =>
    rcases ν with _ | _ | _ | ν <;> simp
  | [(s, ν), (t, μ)] =>
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    rcases ν with _ | _ | _ | ν <;> rcases μ with _ | _ | _ | μ <;> simp
  | _ :: _ :: _ :: _ => simp

/-- A reaction's compiled factor, read at any index with `.general #[]` as the default. -/
theorem compile_getD (net : Network Float) (k : Nat) :
    (net.reactions.map (Gen3.Factor.compile ·.reactants)).getD k (.general #[]) =
      Gen3.Factor.compile net.reactions[k]!.reactants := by
  by_cases h : k < net.reactions.size
  · rw [arr_getElem!_pos net.reactions k h]
    simp [Array.getD, h]
  · rw [arr_getElem!_neg net.reactions k h]
    simp [Array.getD, h]
    rfl

/-- Generation 27's compile is generation 6's. -/
theorem compile27_eq (net : Network Float) : Gen27.compile net = Gen6.compile net := by
  unfold Gen27.compile Gen6.compile Gen5.compile Gen3.compile
  simp only [factorOf_eq, compile_getD]

/-- `setLeaves` writes the upper bounds of reactions `0, …, j - 1` to leaves `P, …, P + j - 1`. -/
theorem setLeaves_data (rxs : Array (Reaction Float)) (hi : Array Nat) (P : Nat) :
    ∀ j (t : FloatArray), P + j ≤ t.data.size →
      (Gen27.setLeaves rxs hi P t j).data.size = t.data.size ∧
      ∀ k, (Gen27.setLeaves rxs hi P t j).data[k]! =
        if P ≤ k ∧ k < P + j then Gen2.rate rxs[k - P]! hi else t.data[k]! := by
  intro j
  induction j with
  | zero =>
    intro t _
    refine ⟨rfl, fun k => ?_⟩
    rw [ite_eq_right (by omega)]
    rfl
  | succ j ih =>
    intro t ht
    have hs : P + j < t.data.size := by omega
    obtain ⟨r1, r2⟩ := ih (t.set! (P + j) (Gen2.rate rxs[j]! hi)) (by simp; omega)
    refine ⟨by simp only [Gen27.setLeaves]; rw [r1]; simp, fun k => ?_⟩
    simp only [Gen27.setLeaves]
    rw [r2 k, floatArray_set!_data, getElem!_set!_eq_ite _ _ _ _ hs]
    by_cases h1 : P ≤ k ∧ k < P + j
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1]
      by_cases h2 : k = P + j
      · subst h2
        rw [ite_eq_left rfl, ite_eq_left (by omega), show P + j - P = j by omega]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- Generation 27's initial tree is `Gen1.buildTree`'s. -/
theorem initialTree_eq (C : Gen3.Compiled) (hi : Array Nat)
    (hm : C.net.reactions.size ≤ 2 ^ C.depth) :
    Gen27.initialTree C hi = Gen1.buildTree (C.net.reactions.map (Gen2.rate · hi)) C.depth := by
  unfold Gen27.initialTree Gen1.buildTree
  dsimp only
  congr 1
  have hsz : (⟨Array.replicate (2 * 2 ^ C.depth) 0⟩ : FloatArray).data.size = 2 * 2 ^ C.depth := by
    simp
  obtain ⟨r1, r2⟩ := setLeaves_data C.net.reactions hi (2 ^ C.depth) C.net.reactions.size
    ⟨Array.replicate (2 * 2 ^ C.depth) 0⟩ (by rw [hsz]; omega)
  suffices h : (Gen27.setLeaves C.net.reactions hi (2 ^ C.depth)
      ⟨Array.replicate (2 * 2 ^ C.depth) 0⟩ C.net.reactions.size).data =
      (Gen1.leafArray (C.net.reactions.map (Gen2.rate · hi)) C.depth).data by
    generalize Gen27.setLeaves C.net.reactions hi (2 ^ C.depth)
      ⟨Array.replicate (2 * 2 ^ C.depth) 0⟩ C.net.reactions.size = a at h
    cases a
    exact congrArg FloatArray.mk h
  apply Array.ext
  · rw [r1, hsz]; simp [Gen1.leafArray]
  · intro k hk1 hk2
    rw [← getElem!_pos _ k hk1, r2 k]
    simp only [Gen1.leafArray, Array.getElem_ofFn, leafOf]
    by_cases hP : 2 ^ C.depth ≤ k
    · rw [ite_eq_left hP]
      by_cases hk : k < 2 ^ C.depth + C.net.reactions.size
      · rw [ite_eq_left ⟨hP, hk⟩, dite_eq_left (by simp; omega), Array.getElem_map,
          arr_getElem!_pos _ _ (by omega)]
      · rw [ite_eq_right (by omega), dite_eq_right (by simp; omega)]
        have hk : k < 2 * 2 ^ C.depth := by rw [r1, hsz] at hk1; exact hk1
        rw [getElem!_pos _ k (by simpa using hk), Array.getElem_replicate]
        rfl
    · rw [ite_eq_right (by omega), ite_eq_right hP]
      have hk : k < 2 * 2 ^ C.depth := by rw [r1, hsz] at hk1; exact hk1
      rw [getElem!_pos _ k (by simpa using hk), Array.getElem_replicate]

/-- Generation 27's start, on a cache without lower bounds, is generation 26's on the cache
with them. -/
theorem start27_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (count : Nat) (trace : Array (Float × State))
    (hlow : c.lower = ⟨C.gen5.base.net.reactions.map (Gen2.rate · c.lo)⟩) :
    Gen27.start C codes horizon save cap fuel pop ⟨c.lo, c.hi, ⟨#[]⟩, c.tree⟩ now rng count
        trace =
      Gen26.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen27.start Gen26.start
  dsimp only
  split
  · rfl
  · congr 1
    cases c
    simp only at hlow ⊢
    rw [hlow]

/-- Generation 27 returns what generation 26 returns, on every network and input. -/
theorem gen27_eq_gen26 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen27.simulate net initial start horizon rng maxEvents save cap =
      Gen26.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen27.simulate Gen26.simulate
  simp only [compile27_eq]
  split
  · rfl
  · split
    · rfl
    · rw [initialTree_eq _ _ (treeDepth_spec _)]
      exact start27_eq _ _ _ _ _ _ _ (Gen3.initialCache (Gen6.compile net).gen5.base initial)
        _ _ _ _ rfl

/-- **Generation 27 is the specification.** For every network whose reactant species are in
range and every input, generation 27 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen27_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen27.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen27_eq_gen26, gen26_simulate_eq net hwf]

end JumpProcessesLean.Proofs
