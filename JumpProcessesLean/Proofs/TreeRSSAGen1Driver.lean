import JumpProcessesLean.Proofs.TreeRSSAGen1

/-!
# Generation 1 driver equals the specification driver
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1

lemma gen1_fire_spec (net : Network Float) (hwf : ReactantsInRange net) (pop : Array Nat) (c : Cache)
    (hc : CacheOK net c) (j : Nat) :
    specState (Gen1.fire (compile net) pop c j).1 (Gen1.fire (compile net) pop c j).2 =
      TreeRSSA.fire net net.maxStoich (specState pop c) j := by
  obtain ⟨f1, f2, f3, _⟩ := fire_ok net hwf pop c hc j
  cases hf : TreeRSSA.fire net net.maxStoich (specState pop c) j
  rw [hf] at f1 f2 f3
  simp only [specState, State.mk.injEq]
  exact ⟨f1, f2, f3⟩

theorem loop_ok (net : Network Float) (hwf : ReactantsInRange net) (horizon : Float) (save : Bool)
    (cap : Nat) :
    ∀ fuel pop c now rng count trace, CacheOK net c →
      Gen1.loop (compile net) horizon save cap fuel pop c now rng count trace =
        TreeRSSA.simulateLoop hostArithmetic hostSource net net.maxStoich horizon save cap fuel
          (specState pop c) now rng count trace := by
  intro fuel
  induction fuel with
  | zero =>
    intro pop c now rng count trace hc
    rw [Gen1.loop, TreeRSSA.simulateLoop, event_ok net pop c hc]
    cases hev : TreeRSSA.event hostArithmetic hostSource net (specState pop c) now rng cap with
    | error err => simp only [bind, Except.bind]
    | ok p =>
      obtain ⟨ev, r⟩ := p
      cases ev with
      | none => simp only [bind, Except.bind, specState]
      | some e => simp only [bind, Except.bind, specState]
  | succ fuel ih =>
    intro pop c now rng count trace hc
    rw [Gen1.loop, TreeRSSA.simulateLoop, event_ok net pop c hc]
    cases hev : TreeRSSA.event hostArithmetic hostSource net (specState pop c) now rng cap with
    | error err => simp only [bind, Except.bind]
    | ok p =>
      obtain ⟨ev, r⟩ := p
      cases ev with
      | none => simp only [bind, Except.bind, specState]
      | some e =>
        simp only [bind, Except.bind]
        rw [← gen1_fire_spec net hwf pop c hc e.reaction,
          ← ih _ _ _ _ _ _ (fire_ok net hwf pop c hc e.reaction).2.2.2]

/-- **Generation 1 is the specification.** For every network whose reactant species are in
range and every input, the optimized implementation returns exactly what the reference
Tree-RSSA returns on host floats with the xoshiro256++ source. -/
theorem gen1_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen1.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save cap := by
  unfold Gen1.simulate TreeRSSA.simulate
  have hinit : CacheOK net (initialCache (compile net) initial) :=
    ⟨rfl, buildTree_ok _ _⟩
  have hspec : specState initial.pop (initialCache (compile net) initial) = initial := rfl
  rw [loop_ok net hwf horizon save cap maxEvents initial.pop _ start rng 0 _ hinit, hspec]

end JumpProcessesLean.Proofs
