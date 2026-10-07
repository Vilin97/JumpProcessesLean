import Std

namespace JumpProcessesLean

/-- Arithmetic has no field-law assumptions: IEEE arithmetic is a valid instance. -/
structure Arithmetic (α : Type) where
  zero : α
  one : α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  lt : α → α → Bool
  le : α → α → Bool
  finite : α → Bool
  ofNat : Nat → α

inductive Error where
  | invalidRate (index : Nat)
  | invalidBounds (index : Nat)
  | invalidUniform
  | invalidExponential
  | invalidTime
  | invalidShape
  | invalidDependency (index : Nat)
  | selectionFailure
  | exhaustedRandomness
  | proposalLimit
  | eventLimit
  | negativePopulation
  | transcendentalFailure
  deriving Repr, BEq, DecidableEq

/-- Randomness is injected. A deterministic PRNG is not an ideal independent source. -/
structure RandomSource (α R : Type) where
  uniform : R → Except Error (α × R)
  exponential : R → Except Error (α × R)

structure Event (α : Type) where
  time : α
  reaction : Nat
  deriving Repr

def validRate {α : Type} (op : Arithmetic α) (x : α) : Bool :=
  op.finite x && op.le op.zero x

def sumRates {α : Type} (op : Arithmetic α) (rates : Array α) : α :=
  rates.foldl op.add op.zero

def checkRatesAux {α : Type} (op : Arithmetic α) : List α → Nat → Except Error Unit
  | [], _ => .ok ()
  | a :: rest, i =>
    if validRate op a then checkRatesAux op rest (i + 1)
    else .error (.invalidRate i)

def checkRates {α : Type} [Inhabited α] (op : Arithmetic α) (rates : Array α) : Except Error Unit :=
  checkRatesAux op rates.toList 0

/-- Strict upper CDF endpoints skip zero-rate channels even when the uniform is zero. -/
def chooseAux {α : Type} (op : Arithmetic α) (x : α) :
    List α → α → Nat → Option Nat
  | [], _, _ => none
  | a :: rest, cumulative, index =>
    let next := op.add cumulative a
    if op.lt op.zero a && op.lt x next then some index
    else chooseAux op x rest next (index + 1)

def weightedIndex {α : Type} (op : Arithmetic α) (rates : Array α)
    (threshold : α) : Except Error Nat :=
  match chooseAux op threshold rates.toList op.zero 0 with
  | some i => .ok i
  | none => .error .selectionFailure

def drawUniform {α R : Type} (op : Arithmetic α) (src : RandomSource α R)
    (rng : R) : Except Error (α × R) := do
  let (u, rng) ← src.uniform rng
  if !(op.finite u && op.le op.zero u && op.lt u op.one) then
    throw .invalidUniform
  return (u, rng)

def drawExponential {α R : Type} (op : Arithmetic α) (src : RandomSource α R)
    (rng : R) : Except Error (α × R) := do
  let (e, rng) ← src.exponential rng
  if !(op.finite e && op.lt op.zero e) then throw .invalidExponential
  return (e, rng)

/-- Finite random tapes support source-independent deterministic regression fixtures. -/
structure Tape (α : Type) where
  uniforms : List α := []
  exponentials : List α := []

def tapeSource (α : Type) : RandomSource α (Tape α) where
  uniform t := match t.uniforms with
    | [] => .error .exhaustedRandomness
    | x :: xs => .ok (x, {t with uniforms := xs})
  exponential t := match t.exponentials with
    | [] => .error .exhaustedRandomness
    | x :: xs => .ok (x, {t with exponentials := xs})

end JumpProcessesLean
