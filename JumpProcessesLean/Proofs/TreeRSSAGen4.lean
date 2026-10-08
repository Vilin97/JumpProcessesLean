import JumpProcessesLean.Proofs.TreeRSSAGen3
import JumpProcessesLean.TreeRSSA.Gen4

/-!
# Generation 4 is generation 3, hence the specification

Generation 4 only reorganizes generation 3's control flow: one call per proposal, the
generator state as four words, the accepted event handled in place. From any proposal, the
fused driver computes what generation 3's loop computes after generation 3's proposals from
that point. No invariant of the cache is needed.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

/-- Generation 3's loop once the event of the current step is known. -/
def afterEvent (C : Gen3.Compiled) (horizon : Float) (save : Bool) (cap fuel : Nat)
    (pop : Array Nat) (c : Cache) (now : Float) (count : Nat) (trace : Array (Float × State)) :
    Except Error (Option (Event Float) × Xoshiro) → Except Error (Solution Float State Xoshiro)
  | .error err => .error err
  | .ok (none, rng) =>
    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
  | .ok (some e, rng) =>
    if !decide (now ≤ e.time) || !e.time.isFinite then .error .invalidTime
    else if !decide (e.time ≤ horizon) then
      .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
    else
      match fuel with
      | 0 => .error .eventLimit
      | f + 1 =>
        let (pop, c) := Gen3.fire C pop c e.reaction
        let trace := if save then trace.push (e.time, ⟨pop, c.lo, c.hi⟩) else trace
        Gen3.loop C horizon save cap f pop c e.time rng (count + 1) trace

lemma loop_afterEvent (C : Gen3.Compiled) (horizon : Float) (save : Bool) (cap fuel : Nat)
    (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) :
    Gen3.loop C horizon save cap fuel pop c now rng count trace =
      afterEvent C horizon save cap fuel pop c now count trace (Gen3.event C pop c now rng cap) := by
  cases fuel with
  | zero =>
    rw [Gen3.loop]
    cases Gen3.event C pop c now rng cap with
    | error err => rfl
    | ok p =>
      obtain ⟨ev, r⟩ := p
      cases ev with
      | none => rfl
      | some e => rfl
  | succ f =>
    rw [Gen3.loop]
    cases Gen3.event C pop c now rng cap with
    | error err => rfl
    | ok p =>
      obtain ⟨ev, r⟩ := p
      cases ev with
      | none => rfl
      | some e => rfl

lemma gen4_fire_eq (C : Gen3.Compiled) (pop : Array Nat) (c : Cache) (j : Nat) :
    Gen4.fire C pop c j = Gen3.fire C pop c j := rfl

lemma xoshiro_eta (r : Xoshiro) : (⟨r.s0, r.s1, r.s2, r.s3⟩ : Xoshiro) = r := rfl

/-- The fused driver from one proposal on, given the statement for the next event. -/
theorem run_eq_of (C : Gen3.Compiled) (horizon : Float) (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen4.run C horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        afterEvent C horizon save cap f pop c now count trace
          (Gen3.proposals C pop c.lower c.tree now total prFuel elapsed ⟨s0, s1, s2, s3⟩)) :
    ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen4.run C horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        afterEvent C horizon save cap fuel pop c now count trace
          (Gen3.proposals C pop c.lower c.tree now total prFuel elapsed ⟨s0, s1, s2, s3⟩) := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen4.run.eq_1, Gen3.proposals]
    rfl
  | succ pf ih =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen4.run.eq_2, Gen3.proposals]
    rcases h1 : Xoshiro.uniform ⟨s0, s1, s2, s3⟩ with ⟨u, r1⟩
    dsimp only
    by_cases hu : (!(u.isFinite && decide (floatZero ≤ u) && decide (u < floatOne))) = true
    · simp only [hu, ↓reduceIte]; rfl
    simp only [hu, Bool.false_eq_true, ↓reduceIte]
    rcases h2 : r1.exponential with ⟨e, r2⟩
    dsimp only
    by_cases he : (!(e.isFinite && decide (floatZero < e))) = true
    · simp only [he, ↓reduceIte]; rfl
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    by_cases hel : (!(elapsed + e).isFinite) = true
    · simp only [hel, ↓reduceIte]; rfl
    simp only [hel, Bool.false_eq_true, ↓reduceIte]
    rcases h3 : r2.uniform with ⟨v, r3⟩
    dsimp only
    by_cases hv : (!(v.isFinite && decide (floatZero ≤ v) && decide (v < floatOne))) = true
    · simp only [hv, ↓reduceIte]; rfl
    simp only [hv, Bool.false_eq_true, ↓reduceIte]
    generalize Gen1.descend c.tree C.depth 1 (u * total) - C.leaves = j
    by_cases hacc : (decide (j < C.numRx) &&
        Gen2.accept (c.lower.get! j) (Gen3.rate C j pop) (v * c.tree.get! (C.leaves + j))) = true
    · simp only [hacc, ↓reduceIte]
      generalize now + (elapsed + e) / total = time
      by_cases ht : (!(time.isFinite && decide (now < time))) = true
      · simp only [ht, ↓reduceIte]; rfl
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      have hfin : time.isFinite = true := by
        revert ht; cases time.isFinite <;> simp
      simp only [afterEvent, hfin, Bool.not_true, Bool.or_false]
      by_cases hle : (!decide (now ≤ time)) = true
      · simp only [hle, ↓reduceIte]
      simp only [hle, Bool.false_eq_true, ↓reduceIte]
      by_cases hh : (!decide (time ≤ horizon)) = true
      · simp only [hh, ↓reduceIte, xoshiro_eta]
      simp only [hh, Bool.false_eq_true, ↓reduceIte]
      cases fuel with
      | zero => rfl
      | succ f =>
        dsimp only
        rw [gen4_fire_eq]
        rcases hf : Gen3.fire C pop c j with ⟨pop', c'⟩
        dsimp only
        rw [loop_afterEvent, Gen3.event]
        by_cases hfin' : (!(c'.tree.get! 1).isFinite) = true
        · simp only [hfin', ↓reduceIte]; rfl
        simp only [hfin', Bool.false_eq_true, ↓reduceIte]
        by_cases hpos : (!decide (floatZero < c'.tree.get! 1)) = true
        · simp only [hpos, ↓reduceIte, xoshiro_eta]; rfl
        simp only [hpos, Bool.false_eq_true, ↓reduceIte]
        rw [hnext f rfl, xoshiro_eta]
    · simp only [hacc, Bool.false_eq_true, ↓reduceIte]
      rw [ih, xoshiro_eta]

theorem run_eq (C : Gen3.Compiled) (horizon : Float) (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen4.run C horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        afterEvent C horizon save cap fuel pop c now count trace
          (Gen3.proposals C pop c.lower c.tree now total prFuel elapsed ⟨s0, s1, s2, s3⟩) := by
  intro fuel
  induction fuel with
  | zero => exact run_eq_of C horizon save cap 0 (fun f h => absurd h (by omega))
  | succ f ih => exact run_eq_of C horizon save cap (f + 1) (fun f' h => by cases h; exact ih)

theorem start_eq (C : Gen3.Compiled) (horizon : Float) (save : Bool) (cap fuel : Nat)
    (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) :
    Gen4.start C horizon save cap fuel pop c now rng count trace =
      Gen3.loop C horizon save cap fuel pop c now rng count trace := by
  rw [loop_afterEvent]
  unfold Gen4.start Gen3.event
  by_cases h1 : (!(c.tree.get! 1).isFinite) = true
  · simp only [h1, ↓reduceIte]; rfl
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : (!decide (floatZero < c.tree.get! 1)) = true
  · simp only [h2, ↓reduceIte]; rfl
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  rw [run_eq, xoshiro_eta]

/-- Generation 4 returns what generation 3 returns, on every network and input. -/
theorem gen4_eq_gen3 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen4.simulate net initial start horizon rng maxEvents save cap =
      Gen3.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen4.simulate Gen3.simulate
  simp only [start_eq]

/-- **Generation 4 is the specification.** For every network whose reactant species are in
range and every input, generation 4 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen4_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen4.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen4_eq_gen3, gen3_simulate_eq net hwf]

end JumpProcessesLean.Proofs
