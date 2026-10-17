import JumpProcessesLean.Proofs.TreeRSSAGen29
import JumpProcessesLean.TreeRSSA.Gen30

/-!
# Generation 30 is generation 29, hence the specification

Generation 30's setup returns generation 29's values. Pushing `f x` for every `x` into a new
array is `map f` (`mapNew_eq`, `ratesOf_eq`, `pickRates_eq`), and a shared change is the change
`Gen6.Change.ofPair` or `ChangeW.ofChange` would build (`changeOf_eq`, `changeWOf_eq`). So the
compiled network is generation 27's (`compile30_eq`), the compiled records generation 18's
(`compileW30_eq`) and the start generation 29's (`start30_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

theorem foldl_push_eq {α β : Type} (f : α → β) : ∀ (l : List α) (acc : Array β),
    l.foldl (fun acc x => acc.push (f x)) acc = acc ++ (l.map f).toArray := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x l ih =>
    intro acc
    rw [List.foldl_cons, ih, List.map_cons]
    apply Array.ext'
    simp

theorem foldl_push_data {α : Type} (f : α → Float) : ∀ (l : List α) (acc : FloatArray),
    (l.foldl (fun acc x => acc.push (f x)) acc).data = acc.data ++ (l.map f).toArray := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x l ih =>
    intro acc
    rw [List.foldl_cons, ih, List.map_cons]
    cases acc
    apply Array.ext'
    simp [FloatArray.push]

/-- Pushing into a new array is `map`. -/
theorem mapNew_eq {α β : Type} (f : α → β) (xs : Array α) : Gen30.mapNew f xs = xs.map f := by
  unfold Gen30.mapNew
  rw [← Array.foldl_toList, foldl_push_eq]
  apply Array.ext'
  simp [Array.emptyWithCapacity]

theorem ratesOf_eq (rxs : Array (Reaction Float)) :
    Gen30.ratesOf rxs = ⟨rxs.map (·.rate)⟩ := by
  unfold Gen30.ratesOf
  apply FloatArray.ext
  rw [← Array.foldl_toList, foldl_push_data]
  apply Array.ext'
  simp [FloatArray.emptyWithCapacity]

theorem pickRates_eq (rates : FloatArray) (ks : Array Nat) :
    Gen30.pickRates rates ks = ⟨ks.map fun k => rates.get! k⟩ := by
  unfold Gen30.pickRates
  apply FloatArray.ext
  rw [← Array.foldl_toList, foldl_push_data]
  apply Array.ext'
  simp [FloatArray.emptyWithCapacity]

theorem mapNew_fun {α β : Type} (f : α → β) : Gen30.mapNew f = Array.map f :=
  funext (mapNew_eq f)

theorem pickRates_fun (rates : FloatArray) :
    Gen30.pickRates rates = fun ks => ⟨ks.map fun k => rates.get! k⟩ :=
  funext (pickRates_eq rates)

/-- Reaction `k`'s rate read from the rates array is its rate, past the last reaction too. -/
theorem rates_get! (rxs : Array (Reaction Float)) (k : Nat) :
    (⟨rxs.map (·.rate)⟩ : FloatArray).get! k = rxs[k]!.rate := by
  simp only [FloatArray.get!]
  by_cases hk : k < rxs.size
  · rw [getElem!_pos (rxs.map (·.rate)) k (by simpa using hk), getElem!_pos rxs k hk,
      Array.getElem_map]
  · rw [getElem!_neg (rxs.map (·.rate)) k (by simpa using hk), getElem!_neg rxs k hk]
    rfl

/-- The shared changes are the changes `Gen6.Change.ofPair` builds. -/
theorem changeOf_eq (n : Nat) (c : Nat × Int) :
    Gen30.changeOf (Gen30.unitChanges n) c = Gen6.Change.ofPair c := by
  unfold Gen30.changeOf Gen30.unitChanges
  split
  · split
    · rename_i h1
      have e : c.2 = 1 := by simpa using h1
      simp [Gen6.Change.ofPair, e]
    · split
      · rename_i _ h2
        have e : c.2 = -1 := by simpa using h2
        simp [Gen6.Change.ofPair, e]
      · rfl
  · rfl

/-- The shared images are the records `ChangeW.ofChange` builds. -/
theorem changeWOf_eq (n : Nat) (ch : Gen6.Change) :
    Gen30.changeWOf (Gen30.unitChangesW n) ch = Gen18.ChangeW.ofChange ch := by
  obtain ⟨s, up, down⟩ := ch
  unfold Gen30.changeWOf Gen30.unitChangesW
  split
  · split
    · rename_i h1
      have e : up = 1 ∧ down = 0 := by simpa using h1
      obtain ⟨rfl, rfl⟩ := e
      simp
    · split
      · rename_i _ h2
        have e : up = 0 ∧ down = 1 := by simpa using h2
        obtain ⟨rfl, rfl⟩ := e
        simp
      · rfl
  · rfl

/-- Generation 30's compiled network is generation 27's. -/
theorem compile30_eq (net : Network Float) : Gen30.compile net = Gen27.compile net := by
  have hc : Gen30.changeOf (Gen30.unitChanges net.numSpecies) = Gen6.Change.ofPair :=
    funext (changeOf_eq net.numSpecies)
  unfold Gen30.compile Gen27.compile
  simp only [ratesOf_eq, pickRates_fun, mapNew_fun, hc, rates_get!]

/-- Generation 30's compiled records are generation 18's. -/
theorem compileW30_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) :
    Gen30.compileW C codes = Gen18.compileW C codes := by
  have hc : Gen30.changeWOf (Gen30.unitChangesW C.gen5.base.ms.size) = Gen18.ChangeW.ofChange :=
    funext (changeWOf_eq C.gen5.base.ms.size)
  unfold Gen30.compileW Gen18.compileW
  simp only [mapNew_fun, hc]

/-- Generation 30's start is generation 29's. -/
theorem start30_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (count : Nat) (trace : Array (Float × State)) :
    Gen30.start C codes horizon save cap fuel pop c now rng count trace =
      Gen29.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen30.start Gen29.start
  simp only [compileW30_eq]

/-- Generation 30 returns what generation 29 returns, on every network and input. -/
theorem gen30_eq_gen29 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen30.simulate net initial start horizon rng maxEvents save cap =
      Gen29.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen30.simulate Gen29.simulate
  simp only [compile30_eq, start30_eq]

/-- **Generation 30 is the specification.** For every network whose reactant species are in
range and every input, generation 30 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen30_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen30.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen30_eq_gen29, gen29_simulate_eq net hwf]

end JumpProcessesLean.Proofs
