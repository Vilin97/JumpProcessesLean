import JumpProcessesLean

/-!
# Benchmark driver

    jumpBench <model.rn> <method> <T> <reps> [maxEvents] [seed]

Prints one JSON object per repetition. Methods:

* `direct-floatlib`, `nrm-floatlib`, `rssa-floatlib`: the verified public driver with
  FloatLib binary64 arithmetic and SplitMix64 (the arithmetic the proofs cover);
* `rssacr-port`: the port of JumpProcesses.jl's RSSACR on host floats;
* `treerssa-spec`: the Tree-RSSA reference specification on host floats;
* `treerssa-g1`, `treerssa-g2`, ...: the optimized generations, each proved equal to the
  specification. Equal seeds give equal runs, which the printed population digest shows.
-/

open JumpProcessesLean

namespace Bench

def floatLibOf (x : Float) : Binary64 :=
  FloatLib.Floats.ExecFloat.Binary.ofNatBits x.toBits.toNat

/-- The network as a public-driver model; brackets are recomputed from each state. -/
def networkModel {α : Type} [Inhabited α] (op : Arithmetic α) (net : Network α) :
    Model α (Array Nat) where
  rates pop := net.reactions.map (TreeRSSA.propensity op · pop)
  transition pop j := do
    let some rx := net.reactions[j]? | throw .invalidShape
    let mut pop := pop
    for (s, d) in rx.changes do
      let value := (pop[s]! : Int) + d
      if value < 0 then throw .negativePopulation
      pop := pop.set! s value.toNat
    return pop
  bounds pop :=
    let lo := pop.map fun n => (populationBracket n).1
    let hi := pop.map fun n => (populationBracket n).2
    ⟨net.reactions.map (TreeRSSA.propensity op · lo), net.reactions.map (TreeRSSA.propensity op · hi)⟩

structure Outcome where
  status : String
  events : Nat
  time : Float
  /-- A hash of the final populations, to compare generations run by run. -/
  digest : UInt64 := 0

def popDigest (pop : Array Nat) : UInt64 :=
  pop.foldl (fun h n => (h ^^^ n.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

def describe {α σ R : Type} (time : α → Float) (digest : σ → UInt64)
    (r : Except Error (Solution α σ R)) (maxEvents : Nat) : Outcome :=
  match r with
  | .ok s => ⟨"ok", s.events, time s.time, digest s.state⟩
  | .error .eventLimit => ⟨"eventLimit", maxEvents, 0, 0⟩
  | .error e => ⟨s!"error {repr e}", 0, 0, 0⟩

def stateDigest (st : TreeRSSA.State) : UInt64 := popDigest st.pop

def hostTime (x : Float) : Float := x

def floatLibTime (x : Binary64) : Float :=
  match FloatLib.Floats.ExecFloat.Binary.toRat? x with
  | some q => q.num.toFloat / q.den.toFloat
  | none => 0

def parseDecimal (text : String) : Option Float :=
  match text.splitOn "." with
  | [a] => a.toNat?.map Nat.toFloat
  | [a, b] => do
    let x ← a.toNat?
    let y ← b.toNat?
    return x.toFloat + y.toFloat / (10 : Float) ^ b.length.toFloat
  | _ => none

def runOnce (netF : Network Float) (netB : Network Binary64) (method : String) (T : Float)
    (maxEvents : Nat) (seed : UInt64) : IO Outcome := do
  match method with
  | "rssacr-port" =>
    let r := Ports.RSSACR.run netF T seed maxEvents
    let status := if r.events ≥ maxEvents then "eventLimit" else "ok"
    return ⟨status, r.events, r.time, popDigest r.pop⟩
  | "treerssa-g1" =>
    let r := TreeRSSA.Gen1.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g2" =>
    let r := TreeRSSA.Gen2.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g3" =>
    let r := TreeRSSA.Gen3.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g4" =>
    let r := TreeRSSA.Gen4.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g5" =>
    let r := TreeRSSA.Gen5.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g6" =>
    let r := TreeRSSA.Gen6.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g7" =>
    let r := TreeRSSA.Gen7.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g8" =>
    let r := TreeRSSA.Gen8.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g9" =>
    let r := TreeRSSA.Gen9.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g10" =>
    let r := TreeRSSA.Gen10.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g11" =>
    let r := TreeRSSA.Gen11.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g12" =>
    let r := TreeRSSA.Gen12.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g13" =>
    let r := TreeRSSA.Gen13.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g14" =>
    let r := TreeRSSA.Gen14.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g15" =>
    let r := TreeRSSA.Gen15.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-g16" =>
    let r := TreeRSSA.Gen16.simulate netF (TreeRSSA.initialState netF netF.initial) 0 T
      (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "treerssa-spec" =>
    let r := TreeRSSA.simulate hostArithmetic hostSource netF
      (TreeRSSA.initialState netF netF.initial) 0 T (Xoshiro.seed seed) maxEvents
    return describe hostTime stateDigest r maxEvents
  | "direct-floatlib" | "nrm-floatlib" | "rssa-floatlib" =>
    let alg := if method == "direct-floatlib" then Algorithm.direct
      else if method == "nrm-floatlib" then Algorithm.nrm else Algorithm.rssa
    let r := simulate binary64Arithmetic binary64Source (networkModel binary64Arithmetic netB) alg
      netB.initial 0 (floatLibOf T) seed maxEvents
    return describe floatLibTime popDigest r maxEvents
  | _ => throw (IO.userError s!"unknown method {method}")

def main (args : List String) : IO UInt32 := do
  match args with
  | path :: method :: tText :: repsText :: rest =>
    let text ← IO.FS.readFile path
    let net ← match parseNetwork text with
      | .ok net => pure net
      | .error e => throw (IO.userError e)
    let netF := net.map Float.ofBits
    let netB := net.map fun bits => FloatLib.Floats.ExecFloat.Binary.ofNatBits bits.toNat
    let some T := parseDecimal tText | throw (IO.userError "bad T")
    let reps := repsText.toNat!
    let maxEvents := (rest.head?.bind String.toNat?).getD 1000000000
    let seed0 := ((rest.drop 1).head?.bind String.toNat?).getD 1
    for rep in [0:reps] do
      let seed := (seed0 + rep).toUInt64
      let t0 ← IO.monoNanosNow
      let o ← runOnce netF netB method T maxEvents seed
      let t1 ← IO.monoNanosNow
      let seconds := (t1 - t0).toFloat / 1e9
      IO.println s!"\{\"model\": \"{path}\", \"method\": \"{method}\", \"T\": {T}, \"seed\": {seed}, \"status\": \"{o.status}\", \"events\": {o.events}, \"seconds\": {seconds}, \"digest\": \"{o.digest}\"}"
      (← IO.getStdout).flush
    return 0
  | _ =>
    IO.eprintln "usage: jumpBench <model.rn> <method> <T> <reps> [maxEvents] [seed]"
    return 1

end Bench

def main (args : List String) : IO UInt32 := Bench.main args
