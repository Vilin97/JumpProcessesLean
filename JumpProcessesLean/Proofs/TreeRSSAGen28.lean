import JumpProcessesLean.Proofs.TreeRSSAGen27
import JumpProcessesLean.TreeRSSA.Gen28

/-!
# Generation 28 is generation 27, hence the specification

Generation 28's start test is generation 27's: comparing the species of up to three changes
decides `List.Nodup` of their list (`distinctSpecies_eq`), so `Gen28.changesOK` is
`Gen17.changesOK` (`changesOK28_eq`) and the rest of the start is generation 27's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA

/-- `distinctSpecies` decides whether the changes name distinct species. -/
theorem distinctSpecies_eq (chs : Array Gen6.Change) :
    Gen28.distinctSpecies chs = decide (chs.toList.map (·.species)).Nodup := by
  obtain ⟨l⟩ := chs
  unfold Gen28.distinctSpecies
  match l with
  | [] => simp
  | [a] => simp
  | [a, b] => by_cases h : a.species = b.species <;> simp [h]
  | [a, b, c] =>
    simp only [List.size_toArray, List.length_cons, List.length_nil, List.map_cons, List.map_nil]
    simp [List.nodup_cons, Bool.and_assoc]
    tauto
  | _ :: _ :: _ :: _ :: _ => simp

/-- Generation 28's `changesOK` is generation 17's. -/
theorem changesOK28_eq (C : Gen6.Compiled) : Gen28.changesOK C = Gen17.changesOK C := by
  unfold Gen28.changesOK Gen17.changesOK
  simp only [distinctSpecies_eq]

/-- Generation 28's start is generation 27's. -/
theorem start28_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Gen1.Cache) (now : Float)
    (rng : Xoshiro) (count : Nat) (trace : Array (Float × State)) :
    Gen28.start C codes horizon save cap fuel pop c now rng count trace =
      Gen27.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen28.start Gen27.start
  simp only [changesOK28_eq]

/-- Generation 28 returns what generation 27 returns, on every network and input. -/
theorem gen28_eq_gen27 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen28.simulate net initial start horizon rng maxEvents save cap =
      Gen27.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen28.simulate Gen27.simulate
  simp only [start28_eq]

/-- **Generation 28 is the specification.** For every network whose reactant species are in
range and every input, generation 28 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen28_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen28.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen28_eq_gen27, gen27_simulate_eq net hwf]

end JumpProcessesLean.Proofs
