import JumpProcessesLean.FloatLibBackend
import JumpProcessesLean.HostFloat
import JumpProcessesLean.Simulation
import JumpProcessesLean.TreeRSSA.Gen17
import JumpProcessesLean.TreeRSSA.Gen18
import JumpProcessesLean.TreeRSSA.Gen19
import JumpProcessesLean.TreeRSSA.Gen20
import JumpProcessesLean.TreeRSSA.Gen21
import JumpProcessesLean.TreeRSSA.Gen22
import JumpProcessesLean.TreeRSSA.Gen23
import JumpProcessesLean.TreeRSSA.Gen24
import JumpProcessesLean.TreeRSSA.Gen25
import JumpProcessesLean.TreeRSSA.Gen26
import JumpProcessesLean.TreeRSSA.Gen27
import JumpProcessesLean.TreeRSSA.Gen28
import JumpProcessesLean.TreeRSSA.Gen29
import JumpProcessesLean.TreeRSSA.Gen30

open JumpProcessesLean

namespace Tests

def expect (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

def getOk {α : Type} (x : Except Error α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"unexpected error: {repr e}")

def expectError {α : Type} (x : Except Error α) (error : Error) (label : String) : IO Unit :=
  match x with
  | .error e => expect (e == error) label
  | .ok _ => throw (IO.userError label)

def near (x : Binary64) (y tolerance : Float) : Bool :=
  match FloatLib.Floats.ExecFloat.Binary.toRat? x with
  | none => false
  | some q => Float.abs (q.num.toFloat / q.den.toFloat - y) < tolerance

def hostValue (x : Binary64) : Float :=
  match FloatLib.Floats.ExecFloat.Binary.toRat? x with
  | none => 0 / 0
  | some q => q.num.toFloat / q.den.toFloat

def deterministic : IO Unit := do
  let op := binary64Arithmetic
  let src := tapeSource Binary64
  let (e, _) ← getOk (direct op src #[1, 3] 0 ⟨[0.75], [2]⟩)
  let some e := e | throw (IO.userError "Direct returned no event")
  expect (e.reaction == 1 && e.time == 0.5) "Direct fixture"
  let (e, _) ← getOk (direct op src #[0, 3, 0] 0 ⟨[0], [3]⟩)
  let some e := e | throw (IO.userError "Direct zero-rate fixture")
  expect (e.reaction == 1 && e.time == 1) "zero-rate channel selected"
  let (e, t) ← getOk (direct op src #[0, 0] 5 {})
  expect (e.isNone && t.uniforms.isEmpty && t.exponentials.isEmpty) "Direct extinction"
  expectError (direct op src #[-1] 0 {}) (.invalidRate 0) "negative rate accepted"
  expectError (direct op src #[1] 0 ⟨[1], [1]⟩) .invalidUniform "uniform endpoint"
  expectError (direct op src #[1] 0 ⟨[0], [0]⟩) .invalidExponential "zero exponential"
  let (s, _) ← getOk (nrmInitialize op src #[2, 4, 0] 0 ⟨[], [4, 12]⟩)
  let some first := nrmNext op s | throw (IO.userError "NRM no first event")
  expect (first.reaction == 0 && first.time == 2) "NRM minimum"
  let (s, tape) ← getOk (nrmUpdate op src s #[1, 8, 3] 0 2 #[0, 1, 1, 2] ⟨[], [1, 6]⟩)
  expect (s.clocks[0]! == some 3 && s.clocks[1]! == some 2.5 && s.clocks[2]! == some 4)
    "NRM fresh/rescale/reactivate"
  expect tape.exponentials.isEmpty "NRM duplicated draws"
  let some next := nrmNext op s | throw (IO.userError "NRM no updated event")
  expect (next.reaction == 1 && next.time == 2.5) "NRM updated minimum"
  let (s, _) ← getOk (nrmUpdate op src s #[0, 0, 3] 1 2.5 #[0, 1] {})
  expect (s.clocks[0]!.isNone && s.clocks[1]!.isNone && s.clocks[2]! == some 4)
    "NRM disable/preserve"
  let (s, _) ← getOk (nrmInitialize op src #[0, 0] 0 {})
  expect (nrmNext op s).isNone "NRM extinction"
  let tied : NRMState Binary64 := ⟨#[0, 1, 0, 1], #[none, some 2, none, some 2]⟩
  let some firstTie := nrmNext op tied | throw (IO.userError "NRM tied clocks")
  expect (firstTie.reaction == 1 && firstTie.time == 2) "NRM tie must choose lowest active index"
  let bounds : RateBounds Binary64 := ⟨#[0, 0], #[2, 2]⟩
  let (e, tape) ← getOk (rssa op src #[1, 0] bounds 0
    ⟨[0.2, 0.75, 0.75, 0.3, 0.2, 0.1], [1, 2, 3]⟩)
  let some e := e | throw (IO.userError "RSSA no accepted event")
  expect (e.reaction == 0 && e.time == 1.5 && tape.uniforms.isEmpty)
    "RSSA did not accumulate rejected clocks"
  let (e, _) ← getOk (rssa op src #[0, 0] bounds 0 {})
  expect e.isNone "RSSA loose-bound extinction"
  expectError (rssa op src #[3, 0] bounds 0 {}) (.invalidBounds 0) "non-enclosing bound"
  expectError (rssa op src #[1] ⟨#[], #[1]⟩ 0 {}) .invalidShape "RSSA mismatched bounds"
  expectError (rssa op src #[1] ⟨#[-1], #[1]⟩ 0 {}) (.invalidBounds 0) "RSSA negative lower bound"
  expectError (rssa op src #[1, 0] bounds 0 ⟨[0.2, 0.75], [1]⟩ 1)
    .proposalLimit "RSSA fuel failure"
  let rx : MassActionReaction Binary64 := ⟨0.5, #[(0, 2)], #[(0, -2), (1, 1)]⟩
  expect ((← getOk (massActionRate op rx #[3, 0])) == 3) "bimolecular rate"
  expect ((← getOk (massActionRate op rx #[1, 0])) == 0) "insufficient reactants"
  expect ((← getOk (massActionTransition rx #[3, 0])) == #[1, 1]) "stoichiometry"
  expectError (massActionTransition rx #[1, 0]) .negativePopulation "population underflow"
  expect (populationBracket 0 == (0, 0) && populationBracket 10 == (6, 14) &&
    populationBracket 100 == (90, 110)) "population brackets"
  IO.println "PASS deterministic fixtures (Direct, NRM, RSSA, validation, mass action)"

def oneEvent (alg : Algorithm) (rng : UInt64) : Except Error (Event Binary64 × UInt64) := do
  let op := binary64Arithmetic
  let src := binary64Source
  match alg with
  | .nrm =>
    let (s, rng) ← nrmInitialize op src #[1, 3] 0 rng
    let some e := nrmNext op s | throw .invalidShape
    pure (e, rng)
  | .direct =>
    let (e, rng) ← direct op src #[1, 3] 0 rng
    let some e := e | throw .invalidShape
    pure (e, rng)
  | .rssa =>
    let (e, rng) ← rssa op src #[1, 3] ⟨#[0, 0], #[2, 6]⟩ 0 rng
    let some e := e | throw .invalidShape
    pure (e, rng)

def distributionTests (samples : Nat := 20000) : IO Unit := do
  for alg in [Algorithm.direct, .nrm, .rssa] do
    let mut rng : UInt64 := 12345
    let mut sum : Float := 0
    let mut sumSq : Float := 0
    let mut marked : Nat := 0
    let mut tail : Nat := 0
    let mut jointTail : Nat := 0
    for _ in [:samples] do
      let (e, r) ← getOk (oneEvent alg rng)
      rng := r
      let t := hostValue e.time
      sum := sum + t
      sumSq := sumSq + t * t
      if e.reaction == 1 then marked := marked + 1
      if t > 0.5 then
        tail := tail + 1
        if e.reaction == 1 then jointTail := jointTail + 1
    let size := samples.toFloat
    let mean := sum / size
    let variance := sumSq / size - mean * mean
    let proportion := marked.toFloat / size
    expect (Float.abs (mean - 0.25) < 0.008) s!"{repr alg}: mean {mean}"
    expect (Float.abs (variance - 0.0625) < 0.007) s!"{repr alg}: variance {variance}"
    expect (Float.abs (proportion - 0.75) < 0.015) s!"{repr alg}: mark {proportion}"
    expect (Float.abs (tail.toFloat / size - Float.exp (-2)) < 0.012) s!"{repr alg}: tail"
    expect (Float.abs (jointTail.toFloat / size - 0.75 * Float.exp (-2)) < 0.012)
      s!"{repr alg}: joint tail"
    IO.println s!"PASS {repr alg}: {samples} clocks, mean={mean}, variance={variance}, P(i=1)={proportion}"

def deathModel (channels : Nat) : Model Binary64 (Array Nat) where
  rates state := (List.range channels).toArray.map fun i =>
    (binary64Arithmetic.ofNat (i + 1) / (10 : Binary64)) * binary64Arithmetic.ofNat state[0]!
  transition state _ := do
    if state[0]! == 0 then throw .negativePopulation
    return #[state[0]! - 1, state[1]! + 1]
  bounds state :=
    let (lo, hi) := populationBracket state[0]!
    let rates n := (List.range channels).toArray.map fun i =>
      (binary64Arithmetic.ofNat (i + 1) / (10 : Binary64)) * binary64Arithmetic.ofNat n
    ⟨rates lo, rates hi⟩

/-- Port of linearreaction_test.jl's 16-channel A→B mean test, with the original
sample count, population, horizon, rate vector, and tolerance. -/
def upstreamLinear (samples : Nat := 8000) : IO Unit := do
  let exact : Float := 100 * Float.exp (-13.6 * 0.1)
  for alg in [Algorithm.direct, .nrm, .rssa] do
    let mut total := 0
    let mut rng : UInt64 := 24680
    for _ in [:samples] do
      let s ← getOk (simulate binary64Arithmetic binary64Source (deathModel 16)
        alg #[100, 0] 0 0.1 rng)
      rng := s.rng
      expect (s.state[0]! + s.state[1]! == 100 && s.time == 0.1) "A→B conservation/horizon"
      total := total + s.state[0]!
    let mean := total.toFloat / samples.toFloat
    expect (Float.abs (mean - exact) < 1) s!"{repr alg}: A→B mean {mean}, expected {exact}"
    IO.println s!"PASS {repr alg}: upstream A→B ({samples} simulations), mean={mean}, expected={exact}"

def extinction : IO Unit := do
  for alg in [Algorithm.direct, .nrm, .rssa] do
    let s ← getOk (simulate binary64Arithmetic binary64Source (deathModel 1)
      alg #[100, 0] 0 1000 111 100000 true)
    expect (s.state == #[0, 100] && s.events == 100 && s.time == 1000)
      s!"{repr alg}: extinction"
    let mut previous : Binary64 := 0
    for (t, _) in s.trace do
      expect (binary64Arithmetic.le previous t) "trace times decreased"
      previous := t
  IO.println "PASS extinction and trace chronology for all three algorithms"

/-- From `2^53` on, consecutive floats are two apart, so a clock step below one rounds back to the
current time. The event then happens at the current time: the clock does not go back and stays
finite, which is all the samplers require. A run from `2^53` must complete. -/
def absorbedClock : IO Unit := do
  let op := binary64Arithmetic
  let src := tapeSource Binary64
  let big : Binary64 := 9007199254740992
  let (e, _) ← getOk (direct op src #[1] big ⟨[0.5], [0.5]⟩)
  let some e := e | throw (IO.userError "Direct absorbed clock")
  expect (e.time == big) "Direct absorbed clock step"
  let (s, _) ← getOk (nrmInitialize op src #[2] big ⟨[], [1]⟩)
  expect (s.clocks[0]! == some big) "NRM absorbed clock step"
  let (e, _) ← getOk (rssa op src #[1] ⟨#[1], #[1]⟩ big ⟨[0.5, 0.5], [0.5]⟩)
  let some e := e | throw (IO.userError "RSSA absorbed clock")
  expect (e.time == big) "RSSA absorbed clock step"
  for alg in [Algorithm.direct, .nrm, .rssa] do
    let s ← getOk (simulate op binary64Source (deathModel 1) alg #[100, 0] big (big + 1048576)
      111 100000 true)
    expect (s.state == #[0, 100] && s.events == 100) s!"{repr alg}: run from 2^53"
  let net : Network Float := ⟨2, #[100, 0], #[⟨0.1, #[(0, 1)], #[(0, -1), (1, 1)]⟩]⟩
  let bigF : Float := 9007199254740992
  let initial := TreeRSSA.initialState net net.initial
  let spec ← getOk (TreeRSSA.simulate hostArithmetic hostSource net initial bigF (bigF + 1048576)
    (Xoshiro.seed 7))
  let fast ← getOk (TreeRSSA.Gen17.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (spec.state.pop == #[0, 100] && spec.events == 100) "Tree-RSSA: run from 2^53"
  expect (fast.state == spec.state && fast.events == spec.events && fast.rng == spec.rng)
    "Tree-RSSA generation 17 differs from the specification from 2^53"
  let words ← getOk (TreeRSSA.Gen18.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (words.state == spec.state && words.events == spec.events && words.rng == spec.rng)
    "Tree-RSSA generation 18 differs from the specification from 2^53"
  let bare ← getOk (TreeRSSA.Gen19.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (bare.state == spec.state && bare.events == spec.events && bare.rng == spec.rng)
    "Tree-RSSA generation 19 differs from the specification from 2^53"
  let bounded ← getOk (TreeRSSA.Gen20.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (bounded.state == spec.state && bounded.events == spec.events && bounded.rng == spec.rng)
    "Tree-RSSA generation 20 differs from the specification from 2^53"
  let records ← getOk (TreeRSSA.Gen21.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (records.state == spec.state && records.events == spec.events && records.rng == spec.rng)
    "Tree-RSSA generation 21 differs from the specification from 2^53"
  let paired ← getOk (TreeRSSA.Gen22.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (paired.state == spec.state && paired.events == spec.events && paired.rng == spec.rng)
    "Tree-RSSA generation 22 differs from the specification from 2^53"
  let paired9 ← getOk (TreeRSSA.Gen23.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (paired9.state == spec.state && paired9.events == spec.events && paired9.rng == spec.rng)
    "Tree-RSSA generation 23 differs from the specification from 2^53"
  let pairEnd ← getOk (TreeRSSA.Gen24.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (pairEnd.state == spec.state && pairEnd.events == spec.events && pairEnd.rng == spec.rng)
    "Tree-RSSA generation 24 differs from the specification from 2^53"
  let noRc ← getOk (TreeRSSA.Gen25.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (noRc.state == spec.state && noRc.events == spec.events && noRc.rng == spec.rng)
    "Tree-RSSA generation 25 differs from the specification from 2^53"
  let oneCh ← getOk (TreeRSSA.Gen26.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (oneCh.state == spec.state && oneCh.events == spec.events && oneCh.rng == spec.rng)
    "Tree-RSSA generation 26 differs from the specification from 2^53"
  let light ← getOk (TreeRSSA.Gen27.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (light.state == spec.state && light.events == spec.events && light.rng == spec.rng)
    "Tree-RSSA generation 27 differs from the specification from 2^53"
  let fastTest ← getOk (TreeRSSA.Gen28.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (fastTest.state == spec.state && fastTest.events == spec.events && fastTest.rng == spec.rng)
    "Tree-RSSA generation 28 differs from the specification from 2^53"
  let walks ← getOk (TreeRSSA.Gen29.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (walks.state == spec.state && walks.events == spec.events && walks.rng == spec.rng)
    "Tree-RSSA generation 29 differs from the specification from 2^53"
  let shared ← getOk (TreeRSSA.Gen30.simulate net initial bigF (bigF + 1048576) (Xoshiro.seed 7))
  expect (shared.state == spec.state && shared.events == spec.events && shared.rng == spec.rng)
    "Tree-RSSA generation 30 differs from the specification from 2^53"
  IO.println "PASS absorbed clock steps from 2^53 (Direct, NRM, RSSA, Tree-RSSA)"

/-- Generation 26 takes its fast path on a network with reactions of one change (a gene's
transcription, degradations, translation) and of two (dimerization), and returns what the
specification returns; generation 25 falls back to generation 20 there. -/
def oneChange : IO Unit := do
  let net : Network Float := ⟨4, #[10, 0, 0, 0], #[⟨1, #[(0, 1)], #[(1, 1)]⟩,
    ⟨0.1, #[(1, 1)], #[(1, -1)]⟩, ⟨0.5, #[(1, 1)], #[(2, 1)]⟩, ⟨0.05, #[(2, 1)], #[(2, -1)]⟩,
    ⟨0.001, #[(2, 2)], #[(2, -2), (3, 1)]⟩, ⟨0.1, #[(3, 1)], #[(3, -1), (2, 2)]⟩]⟩
  let initial := TreeRSSA.initialState net net.initial
  let spec ← getOk (TreeRSSA.simulate hostArithmetic hostSource net initial 0 300 (Xoshiro.seed 3))
  let fast ← getOk (TreeRSSA.Gen26.simulate net initial 0 300 (Xoshiro.seed 3))
  let old ← getOk (TreeRSSA.Gen25.simulate net initial 0 300 (Xoshiro.seed 3))
  let light ← getOk (TreeRSSA.Gen27.simulate net initial 0 300 (Xoshiro.seed 3))
  let fastTest ← getOk (TreeRSSA.Gen28.simulate net initial 0 300 (Xoshiro.seed 3))
  let walks ← getOk (TreeRSSA.Gen29.simulate net initial 0 300 (Xoshiro.seed 3))
  let shared ← getOk (TreeRSSA.Gen30.simulate net initial 0 300 (Xoshiro.seed 3))
  expect (spec.events > 1000) "one-change network: too few events"
  expect (fast.state == spec.state && fast.events == spec.events && fast.rng == spec.rng)
    "Tree-RSSA generation 26 differs from the specification on reactions of one change"
  expect (old.state == spec.state && old.events == spec.events && old.rng == spec.rng)
    "Tree-RSSA generation 25 differs from the specification on reactions of one change"
  expect (light.state == spec.state && light.events == spec.events && light.rng == spec.rng)
    "Tree-RSSA generation 27 differs from the specification on reactions of one change"
  expect (fastTest.state == spec.state && fastTest.events == spec.events && fastTest.rng == spec.rng)
    "Tree-RSSA generation 28 differs from the specification on reactions of one change"
  expect (walks.state == spec.state && walks.events == spec.events && walks.rng == spec.rng)
    "Tree-RSSA generation 29 differs from the specification on reactions of one change"
  expect (shared.state == spec.state && shared.events == spec.events && shared.rng == spec.rng)
    "Tree-RSSA generation 30 differs from the specification on reactions of one change"
  IO.println s!"PASS reactions of one change: generations 25 to 30 match the specification over {spec.events} events"

/-- A word-sized pseudo-random sequence for building test networks (SplitMix64 steps). -/
def nextWord (x : UInt64) : UInt64 × UInt64 := Xoshiro.splitMix x

/-- A pseudo-random number in `[0, n)` and the next state. -/
def below (x : UInt64) (n : Nat) : Nat × UInt64 :=
  let (w, x) := nextWord x
  ((w.toNat % n), x)

/-- A random reaction on `ns` species: one or two distinct reactants of stoichiometry one, or
one of stoichiometry two, and one to three changes, or with `four` sometimes four, which no
fast path takes. -/
def randomReaction (ns : Nat) (four : Bool) (x : UInt64) : Reaction Float × UInt64 := Id.run do
  let (r, x) := below x 1000
  let (shape, x) := below x 3
  let rate := (r + 1).toFloat / (if shape = 0 then 500 else 50000)
  let (a, x) := below x ns
  let (b, x) := below x ns
  let reactants : Array (Nat × Nat) :=
    if shape = 0 then #[(a, 1)] else if shape = 1 ∧ a ≠ b then #[(a, 1), (b, 1)] else #[(a, 2)]
  let (k, x) := below x 10
  let nch := if k < 3 then 1 else if k < 6 then 2 else if k < 9 || !four then 3 else 4
  let mut changes : Array (Nat × Int) := #[]
  let mut x := x
  for _ in [0:nch] do
    let (sp, x1) := below x ns
    let (d, x2) := below x1 4
    x := x2
    if !(changes.any (·.1 == sp)) then
      changes := changes.push (sp, if d < 2 then (d : Int) - 2 else (d : Int) - 1)
  return (⟨rate, reactants, changes⟩, x)

/-- A random network of up to eight species and twenty reactions, with counts below 400. -/
def randomNetwork (four : Bool) (x : UInt64) : Network Float × UInt64 := Id.run do
  let (ns, x) := below x 8
  let ns := ns + 1
  let (nr, x) := below x 20
  let mut x := x
  let mut initial : Array Nat := #[]
  for _ in [0:ns] do
    let (v, x1) := below x 400
    x := x1
    initial := initial.push v
  let mut reactions : Array (Reaction Float) := #[]
  for _ in [0:nr + 1] do
    let (rx, x1) := randomReaction ns four x
    x := x1
    reactions := reactions.push rx
  return (⟨ns, initial, reactions⟩, x)

/-- Generations 25 to 30 against the specification on 200 random networks, a quarter of them
with reactions of four changes: fast paths and fallbacks alike. Networks that grow without
bound reach the event limit; all seven must then report it. -/
def randomNetworks : IO Unit := do
  let mut x : UInt64 := 20261017
  let mut events := 0
  let mut errors := 0
  for i in [0:200] do
    let (net, x1) := randomNetwork (i % 4 == 0) x
    x := x1
    let initial := TreeRSSA.initialState net net.initial
    let spec := TreeRSSA.simulate hostArithmetic hostSource net initial 0 0.2
      (Xoshiro.seed i.toUInt64) 100000
    let g25 := TreeRSSA.Gen25.simulate net initial 0 0.2 (Xoshiro.seed i.toUInt64) 100000
    let g26 := TreeRSSA.Gen26.simulate net initial 0 0.2 (Xoshiro.seed i.toUInt64) 100000
    let g27 := TreeRSSA.Gen27.simulate net initial 0 0.2 (Xoshiro.seed i.toUInt64) 100000
    let g28 := TreeRSSA.Gen28.simulate net initial 0 0.2 (Xoshiro.seed i.toUInt64) 100000
    let g29 := TreeRSSA.Gen29.simulate net initial 0 0.2 (Xoshiro.seed i.toUInt64) 100000
    let g30 := TreeRSSA.Gen30.simulate net initial 0 0.2 (Xoshiro.seed i.toUInt64) 100000
    match spec, g25, g26, g27, g28, g29, g30 with
    | .ok s, .ok a, .ok b, .ok c, .ok d, .ok e, .ok f =>
      expect (a.state == s.state && a.events == s.events && a.rng == s.rng)
        s!"random network {i}: generation 25 differs from the specification"
      expect (b.state == s.state && b.events == s.events && b.rng == s.rng)
        s!"random network {i}: generation 26 differs from the specification"
      expect (c.state == s.state && c.events == s.events && c.rng == s.rng)
        s!"random network {i}: generation 27 differs from the specification"
      expect (d.state == s.state && d.events == s.events && d.rng == s.rng)
        s!"random network {i}: generation 28 differs from the specification"
      expect (e.state == s.state && e.events == s.events && e.rng == s.rng)
        s!"random network {i}: generation 29 differs from the specification"
      expect (f.state == s.state && f.events == s.events && f.rng == s.rng)
        s!"random network {i}: generation 30 differs from the specification"
      events := events + s.events
    | .error e, .error e25, .error e26, .error e27, .error e28, .error e29, .error e30 =>
      expect (e == e25 && e == e26 && e == e27 && e == e28 && e == e29 && e == e30)
        s!"random network {i}: different errors"
      errors := errors + 1
    | _, _, _, _, _, _, _ =>
      throw (IO.userError s!"random network {i}: a run failed where another did not")
  expect (errors < 50) s!"random networks: {errors} runs ended in an error"
  IO.println s!"PASS 200 random networks: generations 25 to 30 match the specification over {events} events ({errors} runs end in the same error)"

/-- Generation 29's refresh walks run on trees of `2^16` leaves or more: a random network of
40,000 reactions on 2,000 species with counts below 20, against generations 28, 30 and 17. A
2,001st species starts at `2^25 - 1` and doubles itself (`A → 2A`), so that the run crosses the
fast path's count bound and generation 29's driver hands over to generation 17's. -/
def deepTree : IO Unit := do
  let mut x : UInt64 := 20261018
  let mut reactions : Array (Reaction Float) := #[]
  for _ in [0:40000] do
    let (rx, x1) := randomReaction 2000 false x
    x := x1
    reactions := reactions.push rx
  let mut initial : Array Nat := #[]
  for _ in [0:2000] do
    let (v, x1) := below x 20
    x := x1
    initial := initial.push v
  let net : Network Float := ⟨2001, initial.push 33554431,
    reactions.push ⟨0.0001, #[(2000, 1)], #[(2000, 1)]⟩⟩
  let init := TreeRSSA.initialState net net.initial
  let g17 ← getOk (TreeRSSA.Gen17.simulate net init 0 0.05 (Xoshiro.seed 11) 1000000)
  let g28 ← getOk (TreeRSSA.Gen28.simulate net init 0 0.05 (Xoshiro.seed 11) 1000000)
  let g29 ← getOk (TreeRSSA.Gen29.simulate net init 0 0.05 (Xoshiro.seed 11) 1000000)
  let g30 ← getOk (TreeRSSA.Gen30.simulate net init 0 0.05 (Xoshiro.seed 11) 1000000)
  expect (g28.events > 1000) s!"tree of 2^16 leaves: only {g28.events} events"
  expect (g29.state == g28.state && g29.events == g28.events && g29.rng == g28.rng)
    "Tree-RSSA generation 29 differs from generation 28 on a tree of 2^16 leaves"
  expect (g30.state == g28.state && g30.events == g28.events && g30.rng == g28.rng)
    "Tree-RSSA generation 30 differs from generation 28 on a tree of 2^16 leaves"
  expect (g17.state == g28.state && g17.events == g28.events && g17.rng == g28.rng)
    "Tree-RSSA generation 17 differs from generation 28 on a tree of 2^16 leaves"
  expect (g29.state.pop[2000]! ≥ 33554432) "tree of 2^16 leaves: the count bound was not crossed"
  -- a saved trace, and the event limit, through generation 29's driver
  let t28 ← getOk (TreeRSSA.Gen28.simulate net init 0 0.002 (Xoshiro.seed 12) 1000000 true)
  let t29 ← getOk (TreeRSSA.Gen29.simulate net init 0 0.002 (Xoshiro.seed 12) 1000000 true)
  let t30 ← getOk (TreeRSSA.Gen30.simulate net init 0 0.002 (Xoshiro.seed 12) 1000000 true)
  expect (t28.trace.size > 10) s!"tree of 2^16 leaves: a trace of {t28.trace.size} states"
  expect (t29.trace == t28.trace && t30.trace == t28.trace && t29.rng == t28.rng &&
      t30.rng == t28.rng)
    "Tree-RSSA generations 29 and 30 differ from generation 28 in a trace on a tree of 2^16 leaves"
  match TreeRSSA.Gen28.simulate net init 0 0.05 (Xoshiro.seed 13) 500,
      TreeRSSA.Gen29.simulate net init 0 0.05 (Xoshiro.seed 13) 500,
      TreeRSSA.Gen30.simulate net init 0 0.05 (Xoshiro.seed 13) 500 with
  | .error e28, .error e29, .error e30 =>
    expect (e28 == .eventLimit && e29 == e28 && e30 == e28)
      "tree of 2^16 leaves: different errors at the event limit"
  | _, _, _ => throw (IO.userError "tree of 2^16 leaves: the event limit was not reached")
  IO.println s!"PASS a tree of 2^16 leaves: generations 17, 28, 29 and 30 agree over {g28.events} events, across the count bound 2^25, in a trace of {t28.trace.size} states and at the event limit"

/-- Moments and tail frequencies of `n` host exponential draws: the sum, the sum of squares,
the counts above 1, 5 and 8 (beyond the ziggurat's base layer at 7.697), and whether every
draw was positive and finite. -/
def hostExpStats : Nat → Xoshiro → Float → Float → Nat → Nat → Nat → Bool →
    Float × Float × Nat × Nat × Nat × Bool
  | 0, _, s1, s2, c1, c5, c8, ok => (s1, s2, c1, c5, c8, ok)
  | n + 1, rng, s1, s2, c1, c5, c8, ok =>
    let (e, rng) := rng.exponential
    hostExpStats n rng (s1 + e) (s2 + e * e) (if e > 1 then c1 + 1 else c1)
      (if e > 5 then c5 + 1 else c5) (if e > 8 then c8 + 1 else c8)
      (ok && e > 0 && e < 1000)

/-- The host source's ziggurat exponential against `Exp(1)`: tolerances are about six
standard errors for two million draws. -/
def hostExponential : IO Unit := do
  let n := 2000000
  let (s1, s2, c1, c5, c8, ok) := hostExpStats n (Xoshiro.seed 12345) 0 0 0 0 0 true
  let size := n.toFloat
  expect ok "host exponential: a draw was not positive and finite"
  expect (Float.abs (s1 / size - 1) < 0.004) s!"host exponential mean {s1 / size}"
  expect (Float.abs (s2 / size - 2) < 0.02) s!"host exponential second moment {s2 / size}"
  expect (Float.abs (c1.toFloat / size - Float.exp (-1)) < 0.002) "host exponential P(E > 1)"
  expect (Float.abs (c5.toFloat / size - Float.exp (-5)) < 0.0004) "host exponential P(E > 5)"
  expect (Float.abs (c8.toFloat / size - Float.exp (-8)) < 0.0001) "host exponential P(E > 8)"
  IO.println s!"PASS host ziggurat exponential: mean {s1 / size}, P(E > 8) {c8.toFloat / size}"

end Tests

def main : IO Unit := do
  Tests.deterministic
  (← IO.getStdout).flush
  Tests.distributionTests
  (← IO.getStdout).flush
  Tests.upstreamLinear
  (← IO.getStdout).flush
  Tests.extinction
  (← IO.getStdout).flush
  Tests.absorbedClock
  (← IO.getStdout).flush
  Tests.oneChange
  (← IO.getStdout).flush
  Tests.randomNetworks
  (← IO.getStdout).flush
  Tests.deepTree
  (← IO.getStdout).flush
  Tests.hostExponential
  IO.println "All tests passed."
