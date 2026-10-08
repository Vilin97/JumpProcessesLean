import JumpProcessesLean.HostFloat
import JumpProcessesLean.TreeRSSA

/-!
# RSSACR, ported from JumpProcesses.jl

A port of `RSSACRJumpAggregation` (JumpProcesses.jl 9.33.1, `src/aggregators/rssacr.jl`,
`prioritytable.jl`, `bracketing.jl`), the fastest exact aggregator of the Catalyst paper's
benchmarks on large networks. It runs on host `Float` with the xoshiro256++ source. It is
an executable reference for benchmarking and is not part of the verified code.

* Brackets: `[0,0]` at zero, `[max(u-4,0), u+4]` below 25, `[trunc(0.9u), trunc(1.1u)]`.
* Proposals: composition–rejection over the upper bounds. Groups hold bounds in
  `[2^k m, 2^{k+1} m)` with `m = 2^exponent(1e-12)`; a group is chosen by a linear search
  from the largest group, a member by rejection inside the group.
* Thinning: accept on `u·high ≤ low` (if `low > 0`), else on `u·high ≤ rate`.
* Time: `t + Σ Exp(1) / Σ high` over all proposals of the event.

Arrays are threaded through tail-recursive loops so that every update is in place.
-/

namespace JumpProcessesLean.Ports.RSSACR

open JumpProcessesLean.TreeRSSA (combinations)

/-- Julia's `exponent` for positive normal floats. -/
@[inline] def exponentOf (x : Float) : Int :=
  ((x.toBits >>> 52) &&& 0x7ff).toNat - 1023

/-- `priortogid` with `mingid = exponent(2^exponent(1e-12)) = -40` (1-based group ids). -/
@[inline] def groupOf (priority : Float) : Nat :=
  if priority ≤ twoPowNeg52 then 1
  else
    let gid := exponentOf priority + 1
    if gid ≤ -40 then 2 else (gid + 40 + 2).toNat

def nineTenths : Float := 0.9
def elevenTenths : Float := 1.1
/-- `2^exponent(1e-12) = 2^-40`, the smallest group bound. -/
def minRate : Float := 9.094947017729282e-13

@[inline] def specBracket (u : Nat) : Nat × Nat :=
  if u = 0 then (0, 0)
  else if u < 25 then (u - 4, u + 4)
  else ((nineTenths * natToFloat u).toUInt64.toNat, (elevenTenths * natToFloat u).toUInt64.toNat)

@[inline] def rate (rx : Reaction Float) (pop : Array Nat) : Float :=
  rx.rate * natToFloat (combinations rx.reactants pop)

/-- The priority table; group ids are 1-based, index 0 is unused. -/
structure Table where
  bound : FloatArray
  members : Array (Array Nat)
  size : Array Nat
  sums : FloatArray
  total : Float
  groupOfPid : Array Nat
  slotOfPid : Array Nat
  deriving Inhabited

namespace Table

/-- Groups `{0}`, `(0, m)`, `[m, 2m)` as in `PriorityTable(ratetogroup, zeros(1), m, 2m)`. -/
def empty (numPids : Nat) : Table :=
  ⟨⟨#[floatZero, floatZero, minRate, 2 * minRate]⟩, #[#[], #[], #[], #[]], #[0, 0, 0, 0],
    ⟨#[floatZero, floatZero, floatZero, floatZero]⟩, floatZero,
    Array.replicate numPids 0, Array.replicate numPids 0⟩

/-- `padtable!`: add groups until the priority lies below the largest bound. -/
partial def pad (t : Table) (priority : Float) : Table :=
  match t with
  | ⟨bound, members, size, sums, total, gp, sp⟩ =>
    let top := bound.get! (bound.size - 1)
    if priority ≥ top then
      pad ⟨bound.push (top + top), members.push #[], size.push 0, sums.push floatZero, total, gp, sp⟩
        priority
    else ⟨bound, members, size, sums, total, gp, sp⟩

@[inline] def placeMember (members : Array (Array Nat)) (gid slot pid : Nat) : Array (Array Nat) :=
  members.modify gid fun m => if slot < m.size then m.set! slot pid else m.push pid

def insert (t : Table) (pid : Nat) (priority : Float) : Table :=
  let gid := groupOf priority
  let t := if priority ≥ t.bound.get! (t.bound.size - 1) then t.pad priority else t
  match t with
  | ⟨bound, members, size, sums, total, gp, sp⟩ =>
    let slot := size[gid]!
    ⟨bound, placeMember members gid slot pid, size.set! gid (slot + 1),
      sums.set! gid (sums.get! gid + priority), total + priority, gp.set! pid gid, sp.set! pid slot⟩

def update (t : Table) (pid : Nat) (old new : Float) : Table :=
  let oldGid := groupOf old
  let newGid := groupOf new
  let t := if new ≥ t.bound.get! (t.bound.size - 1) then t.pad new else t
  match t with
  | ⟨bound, members, size, sums, total, gp, sp⟩ =>
    let total := total + (new - old)
    if oldGid == newGid then
      ⟨bound, members, size, sums.set! newGid (sums.get! newGid + (new - old)), total, gp, sp⟩
    else
      -- remove from the old group by swapping in its last member
      let slot := sp[pid]!
      let last := size[oldGid]! - 1
      let moved := members[oldGid]![last]!
      let members := members.modify oldGid (·.set! slot moved)
      let sp := sp.set! moved slot
      let size := size.set! oldGid last
      let sums := sums.set! oldGid (if last == 0 then floatZero else sums.get! oldGid - old)
      -- insert into the new group
      let newSlot := size[newGid]!
      ⟨bound, placeMember members newGid newSlot pid, size.set! newGid (newSlot + 1),
        sums.set! newGid (sums.get! newGid + new), total, gp.set! pid newGid, sp.set! pid newSlot⟩

/-- Linear search for a group from the largest one; `0` if none. -/
@[specialize] def findGroup (sums : FloatArray) : Nat → Float → Nat
  | 0, _ => 0
  | i + 1, r =>
    if i = 0 then 0
    else
      let r := r - sums.get! i
      if r ≤ floatZero then i else findGroup sums i r

/-- Rejection sampling inside group `gid`; returns `pid + 1`. -/
partial def within (members : Array Nat) (n bound : Float) (high : FloatArray) (rng : Xoshiro) :
    Nat × Xoshiro :=
  let (u, rng) := rng.uniform
  let r := u * n
  let k := r.toUInt64.toNat
  let pid := members[k]!
  if (r - natToFloat k) * bound < high.get! pid then (pid + 1, rng) else within members n bound high rng

/-- `sample(pt, priorities, rng)`; `0` means no reaction. -/
@[inline] def sample (t : Table) (high : FloatArray) (rng : Xoshiro) : Nat × Xoshiro :=
  if t.total < twoPowNeg52 then (0, rng)
  else
    let (u, rng) := rng.uniform
    let gid := findGroup t.sums t.sums.size (u * t.total)
    if gid == 0 then (0, rng)
    else within t.members[gid]! (natToFloat t.size[gid]!) (t.bound.get! gid) high rng

end Table

structure Compiled where
  net : Network Float
  vartojumps : Array (Array Nat)

structure Result where
  pop : Array Nat
  time : Float
  events : Nat
  proposals : Nat
  deriving Inhabited

/-- Bounds of the dependents `deps[i:]` of a refreshed species. -/
def refreshDeps (C : Compiled) (deps : Array Nat) (lo hi : Array Nat) :
    Nat → FloatArray → FloatArray → Table → FloatArray × FloatArray × Table
  | 0, low, high, table => (low, high, table)
  | n + 1, low, high, table =>
    let k := deps[deps.size - (n + 1)]!
    let rx := C.net.reactions[k]!
    let old := high.get! k
    let new := rate rx hi
    refreshDeps C deps lo hi n (low.set! k (rate rx lo)) (high.set! k new) (table.update k old new)

/-- `update_dependent_rates!` over the species changed by the fired reaction. -/
def refreshSpecies (C : Compiled) (changes : Array (Nat × Int)) (pop : Array Nat) :
    Nat → Array Nat → Array Nat → FloatArray → FloatArray → Table →
      Array Nat × Array Nat × FloatArray × FloatArray × Table
  | 0, lo, hi, low, high, table => (lo, hi, low, high, table)
  | n + 1, lo, hi, low, high, table =>
    let s := changes[changes.size - (n + 1)]!.1
    let u := pop[s]!
    if u == 0 || u < lo[s]! || u > hi[s]! then
      let (l, h) := specBracket u
      let lo := lo.set! s l
      let hi := hi.set! s h
      let deps := C.vartojumps[s]!
      let (low, high, table) := refreshDeps C deps lo hi deps.size low high table
      refreshSpecies C changes pop n lo hi low high table
    else refreshSpecies C changes pop n lo hi low high table

def applyChanges (changes : Array (Nat × Int)) : Nat → Array Nat → Array Nat
  | 0, pop => pop
  | n + 1, pop =>
    let (s, d) := changes[changes.size - (n + 1)]!
    applyChanges changes n (pop.set! s (((pop[s]! : Int) + d).toNat))

/-- The proposal loop of `generate_jumps!`; returns the accepted reaction and `Σ Exp(1)`. -/
partial def thin (C : Compiled) (pop : Array Nat) (low high : FloatArray) (table : Table)
    (j : Nat) (rerl : Float) (proposals : Nat) (rng : Xoshiro) : Nat × Float × Nat × Xoshiro :=
  let (u, rng) := rng.uniform
  let r2 := u * high.get! j
  let crlow := low.get! j
  if crlow > floatZero && r2 ≤ crlow then (j, rerl, proposals, rng)
  else
    let crate := rate C.net.reactions[j]! pop
    if crate > floatZero && r2 ≤ crate then (j, rerl, proposals, rng)
    else
      let (jid, rng) := table.sample high rng
      let (e, rng) := rng.exponential
      thin C pop low high table (jid - 1) (rerl + e) (proposals + 1) rng

partial def loop (C : Compiled) (horizon : Float) (maxEvents : Nat) (pop lo hi : Array Nat)
    (low high : FloatArray) (table : Table) (rng : Xoshiro) (t : Float) (events proposals : Nat) :
    Result :=
  if events ≥ maxEvents then ⟨pop, t, events, proposals⟩
  else
    let sumRate := table.total
    if sumRate < twoPowNeg52 then ⟨pop, t, events, proposals⟩
    else
      let (jid, rng) := table.sample high rng
      if jid == 0 then ⟨pop, t, events, proposals⟩
      else
        let (e, rng) := rng.exponential
        let (j, rerl, proposals, rng) := thin C pop low high table (jid - 1) e (proposals + 1) rng
        let next := t + rerl / sumRate
        if next ≥ horizon then ⟨pop, t, events, proposals⟩
        else
          let changes := C.net.reactions[j]!.changes
          let pop := applyChanges changes changes.size pop
          let (lo, hi, low, high, table) :=
            refreshSpecies C changes pop changes.size lo hi low high table
          loop C horizon maxEvents pop lo hi low high table rng next (events + 1) proposals

/-- Simulate on `(0, horizon)` with at most `maxEvents` events. -/
def run (net : Network Float) (horizon : Float) (seed : UInt64) (maxEvents : Nat) : Result :=
  let C : Compiled := ⟨net, net.speciesDependents⟩
  let pop := net.initial
  let lo := pop.map fun u => (specBracket u).1
  let hi := pop.map fun u => (specBracket u).2
  let low : FloatArray := ⟨net.reactions.map (rate · lo)⟩
  let high : FloatArray := ⟨net.reactions.map (rate · hi)⟩
  let table := (List.range net.reactions.size).foldl (fun t j => t.insert j (high.get! j))
    (Table.empty net.reactions.size)
  loop C horizon maxEvents pop lo hi low high table (Xoshiro.seed seed) floatZero 0 0

end JumpProcessesLean.Ports.RSSACR
