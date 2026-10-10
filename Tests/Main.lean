import JumpProcessesLean.FloatLibBackend
import JumpProcessesLean.HostFloat
import JumpProcessesLean.Simulation

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
  Tests.hostExponential
  IO.println "All tests passed."
