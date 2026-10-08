import JumpProcessesLean.Simulation

/-!
# Mass-action reaction networks

A network has a fixed species list with initial populations and mass-action reactions.
Reaction `j` has rate constant `k_j` (statistical factors included) and propensity
`k_j * Π_s n_s (n_s - 1) ⋯ (n_s - ν_s + 1)` over its distinct reactant species `s` with
stoichiometry `ν_s`. Firing it adds its net changes to the populations.

`parseNetwork` reads the plain `.rn` format written by `bench/scripts/net2rn.py`; rate
constants are stored as IEEE binary64 bit patterns.
-/

namespace JumpProcessesLean

structure Reaction (α : Type) where
  rate : α
  /-- Distinct reactant species with their stoichiometry. -/
  reactants : Array (Nat × Nat)
  /-- Net population change of every species that changes. -/
  changes : Array (Nat × Int)
  deriving Inhabited

structure Network (α : Type) where
  numSpecies : Nat
  initial : Array Nat
  reactions : Array (Reaction α)
  deriving Inhabited

namespace Network

def map {α β : Type} (f : α → β) (net : Network α) : Network β :=
  { net with reactions := net.reactions.map fun rx => { rx with rate := f rx.rate } }

/-- Largest stoichiometry with which each species appears as a reactant (`0` if never). -/
def maxStoich {α : Type} (net : Network α) : Array Nat :=
  net.reactions.foldl (init := Array.replicate net.numSpecies 0) fun acc rx =>
    rx.reactants.foldl (init := acc) fun acc (s, ν) =>
      if s < acc.size then acc.set! s (max acc[s]! ν) else acc

/-- Record reaction `j` as a dependent of every reactant species `p.1`. -/
def addDependent (j : Nat) (deps : Array (Array Nat)) (p : Nat × Nat) : Array (Array Nat) :=
  if p.1 < deps.size then deps.modify p.1 (·.push j) else deps

/-- For every species, the reactions that use it as a reactant, in increasing order. -/
def speciesDependents {α : Type} (net : Network α) : Array (Array Nat) :=
  (List.range net.reactions.size).foldl (init := Array.replicate net.numSpecies #[]) fun deps j =>
    match net.reactions[j]? with
    | some rx => rx.reactants.foldl (addDependent j) deps
    | none => deps

/-- Structural well-formedness: populations and every species index fit the species list. -/
def WellFormed {α : Type} (net : Network α) : Prop :=
  net.initial.size = net.numSpecies ∧
    ∀ rx ∈ net.reactions.toList, (∀ p ∈ rx.reactants.toList, p.1 < net.numSpecies) ∧
      ∀ p ∈ rx.changes.toList, p.1 < net.numSpecies

end Network

/-! ### The `.rn` text format -/

private def parseNat (token : String) : Except String Nat :=
  match token.toNat? with
  | some n => .ok n
  | none => .error s!"expected a natural number, got '{token}'"

private def parseInt (token : String) : Except String Int :=
  match token.toInt? with
  | some n => .ok n
  | none => .error s!"expected an integer, got '{token}'"

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseHex (token : String) : Except String UInt64 := do
  if token.isEmpty || token.length > 16 then throw s!"bad rate bits '{token}'"
  let mut value : Nat := 0
  for c in token.toList do
    match hexDigit c with
    | some d => value := 16 * value + d
    | none => throw s!"bad hexadecimal digit in '{token}'"
  return value.toUInt64

private def words (line : String) : List String :=
  (line.splitOn " ").filter (· ≠ "")

private def parseReaction (line : String) : Except String (Reaction UInt64) := do
  match words line with
  | bits :: r :: rest =>
    let rate ← parseHex bits
    let r ← parseNat r
    let mut rest := rest
    let mut reactants := #[]
    for _ in [0:r] do
      match rest with
      | s :: ν :: tail =>
        reactants := reactants.push (← parseNat s, ← parseNat ν)
        rest := tail
      | _ => throw s!"truncated reactant list: {line}"
    let c ← match rest with
      | c :: tail => do rest := tail; parseNat c
      | [] => throw s!"missing change count: {line}"
    let mut changes := #[]
    for _ in [0:c] do
      match rest with
      | s :: d :: tail =>
        changes := changes.push (← parseNat s, ← parseInt d)
        rest := tail
      | _ => throw s!"truncated change list: {line}"
    if !rest.isEmpty then throw s!"trailing tokens: {line}"
    return ⟨rate, reactants, changes⟩
  | _ => throw s!"bad reaction line: {line}"

/-- Parse a `.rn` network; rate constants are returned as binary64 bit patterns. -/
def parseNetwork (text : String) : Except String (Network UInt64) := do
  let lines := (text.splitOn "\n").filter (fun l => !l.trimAscii.isEmpty)
  match lines with
  | header :: speciesLine :: populationLine :: reactionsLine :: rest =>
    if header.trimAscii.toString != "jprn 1" then throw "not a jprn 1 file"
    let numSpecies ← match words speciesLine with
      | ["species", n] => parseNat n
      | _ => throw "bad species line"
    let initial ← (words populationLine).toArray.mapM parseNat
    if initial.size != numSpecies then throw "population count does not match species count"
    let numReactions ← match words reactionsLine with
      | ["reactions", n] => parseNat n
      | _ => throw "bad reactions line"
    let reactions ← rest.toArray.mapM parseReaction
    if reactions.size != numReactions then throw "reaction count mismatch"
    for rx in reactions do
      for (s, _) in rx.reactants do
        if s ≥ numSpecies then throw "reactant species out of range"
      for (s, _) in rx.changes do
        if s ≥ numSpecies then throw "changed species out of range"
    return ⟨numSpecies, initial, reactions⟩
  | _ => throw "truncated header"

end JumpProcessesLean
