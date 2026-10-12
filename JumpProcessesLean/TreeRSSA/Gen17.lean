import JumpProcessesLean.TreeRSSA.Gen16

/-!
# Tree-RSSA, generation 17: one firing loop, machine-word counters, fewer tests

After generation 16 a typical accepted proposal on the smallest network ran about 575
instructions. A third of them were firing: two calls, one applying the changes and one reading
every changed species' bracket again, about sixty instructions per change on boxed natural
numbers. Another hundred were bookkeeping on natural numbers: the proposal and event fuel, the
event count, and the reaction index that the descent's leaf is turned into, each tested for
being small at every use.

Generation 17 fires in one loop. A change only adds or only removes, so it takes one natural-
number operation, and before an event no species is outside its bracket, so only the side the
species moved to can make it stale: an addition leaves it only above `hi`, a removal only below
`lo` or below the maximal stoichiometry. The loop returns the populations with one extra entry
when some species left its bracket; then generation 16's refresh fold runs, otherwise the cache
is kept, and with it the total, which was tested when it was computed. The fuel, the count and
the reaction index are machine words, and of the range tests of the uniforms, the exponential
and the event time only those remain that imply the others.

These shortcuts need facts about the network and the start: each reaction's changes name
distinct species and each only adds or only removes; no species starts outside its bracket; the
counts fit in machine words. They are tested once; otherwise generation 16 runs. The result is
generation 16's (`Proofs/TreeRSSAGen17.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen17

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)

/-- Generation 11's word descent, compiled in this module so that the driver inlines it. -/
def descendW (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) : USize :=
  if hk : k < P then
    have hk' : k.toNat < P.toNat := hk
    have h2 : (2 * k).toNat < tree.size := by rw [Gen11.usize_two_mul k (by omega)]; omega
    let left := tree.uget (2 * k) h2
    if x < left then
      descendW tree P hP hP2 (2 * k) (by rw [Gen11.usize_two_mul k (by omega)]; omega) x
    else
      descendW tree P hP hP2 (2 * k + 1) (by rw [Gen11.usize_two_mul_add_one k (by omega)]; omega)
        (x - left)
  else k
termination_by P.toNat - k.toNat
decreasing_by
  · have := (show k.toNat < P.toNat from hk)
    rw [Gen11.usize_two_mul k (by omega)]; omega
  · have := (show k.toNat < P.toNat from hk)
    rw [Gen11.usize_two_mul_add_one k (by omega)]; omega

/-- Apply the changes `chs[i], chs[i+1], …` to the populations and test each changed species'
bracket on the side it moved to. The result has one extra entry if some species left its bracket.
-/
def applyTest (chs : Array Gen6.Change) (n : Nat) (hv : ∀ k (h : k < chs.size), chs[k].species < n)
    (ms lo hi : Array Nat) (hms : ms.size = n) (hlo : lo.size = n) (hhi : hi.size = n) (i : USize)
    (pop : Array Nat) (hp : pop.size = n) (stale : Bool) : Array Nat :=
  if h : i < chs.usize then
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    let ch := chs.uget i hi'
    have hs : ch.species < n := hv _ hi'
    let s := ch.species
    let old := pop[s]'(by omega)
    if ch.down = 0 then
      let v := old + ch.up
      applyTest chs n hv ms lo hi hms hlo hhi (i + 1) (pop.set s v (by omega))
        (by simp [hp]) (stale || decide (hi[s]'(by omega) < v))
    else
      let v := old - ch.down
      applyTest chs n hv ms lo hi hms hlo hhi (i + 1) (pop.set s v (by omega))
        (by simp [hp]) (stale || decide (v < lo[s]'(by omega)) ||
          (decide (v < ms[s]'(by omega)) && hi[s]'(by omega) != v))
  else if stale then pop.push 0 else pop
termination_by chs.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize chs i h]; omega)

theorem applyTest_size (chs : Array Gen6.Change) (n : Nat)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (ms lo hi : Array Nat) (hms : ms.size = n)
    (hlo : lo.size = n) (hhi : hi.size = n) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ (pop : Array Nat) (hp : pop.size = n) (stale : Bool),
      (applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale).size = n ∨
        (applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale).size = n + 1 := by
  intro m
  induction m with
  | zero =>
    intro i hm pop hp stale
    rw [applyTest]
    split
    · rename_i h; have := Gen15.lt_size_of_lt_usize chs i h; omega
    · split
      · right; simp [hp]
      · left; exact hp
  | succ m ih =>
    intro i hm pop hp stale
    rw [applyTest]
    split
    · rename_i h
      have h1 := Gen15.succ_toNat_of_lt_usize chs i h
      dsimp only
      split
      · exact ih (i + 1) (by omega) _ _ _
      · exact ih (i + 1) (by omega) _ _ _
    · split
      · right; simp [hp]
      · left; exact hp

theorem lt_size_of_lt_usize (a : FloatArray) (i : USize) (h : i < a.usize) : i.toNat < a.size := by
  have h1 : i.toNat < a.usize.toNat := h
  have h2 : a.usize.toNat ≤ a.size := by
    simp only [FloatArray.usize, Nat.toUSize, USize.toNat_ofNat']
    exact Nat.mod_le _ _
  omega

/-- `a.get! i.toNat`, read without tests when `i` is below the array's size as a word. -/
@[inline] def fget (a : FloatArray) (i : USize) : Float :=
  if h : i < a.usize then a.uget i (lt_size_of_lt_usize a i h) else a.get! i.toNat

/-- `a[i.toNat]!`, read without tests when `i` is below the array's size as a word. -/
@[inline] def aget {α : Type} [Inhabited α] (a : Array α) (i : USize) : α :=
  if h : i < a.usize then a.uget i (Gen15.lt_size_of_lt_usize a i h) else a[i.toNat]!

/-- The compiled changes of reaction `j`, with their species in range. -/
@[inline] def changesAt (C : Gen6.Compiled) (n : Nat) (hval : Gen15.ValidChanges C n) (j : USize) :
    {chs : Array Gen6.Change // ∀ k (h : k < chs.size), chs[k].species < n} :=
  if h : j < C.changes.usize then
    have hj := Gen15.lt_size_of_lt_usize C.changes j h
    have he : C.changes[j.toNat]! = C.changes.uget j hj := by
      rw [getElem!_pos C.changes j.toNat hj]; rfl
    have key : ∀ (a b : Array Gen6.Change) (e : a = b) (k : Nat) (ha : k < a.size)
        (hb : k < b.size), a[k].species < n → b[k].species < n := by
      intro a b e; subst e; intro _ _ _ h; exact h
    ⟨C.changes.uget j hj, fun k hk => key _ _ he k (by rw [he]; exact hk) hk
      (hval j.toNat k (by rw [he]; exact hk))⟩
  else ⟨C.changes[j.toNat]!, hval j.toNat⟩

/-- Every reaction's changes name distinct species, and each change only adds or only removes. -/
def changesOK (C : Gen6.Compiled) : Bool :=
  C.changes.all fun chs =>
    chs.all (fun ch => ch.up == 0 || ch.down == 0) && decide (chs.toList.map (·.species)).Nodup

/-- No species is outside its bracket. -/
def inBrackets (ms pop lo hi : Array Nat) : Bool :=
  (List.range ms.size).all fun s => !Gen9.staleI ms[s]! pop[s]! lo[s]! hi[s]!

/-- The driver. The fuel, the count, the reaction count and the tree's leaf count `P` are machine
words; if the tree's size test fails the proposal is generation 16's. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (ms : Array Nat) (n : Nat)
    (hms : ms.size = n) (hval : Gen15.ValidChanges C n) (numRx : USize) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (rates : FloatArray) (factors : Array Gen3.Factor)
    (horizon : Float) (save : Bool) (cap : USize) (evFuel prFuel : USize) (pop : Array Nat)
    (hpop : pop.size = n) (c : Cache) (hlo : c.lo.size = n) (hhi : c.hi.size = n)
    (now total elapsed : Float) (s0 s1 s2 s3 : UInt64) (count : USize)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  if hz : prFuel = 0 then .error .proposalLimit
  else
    if hT : 2 * P ≤ c.tree.usize then
    let rng : Xoshiro := ⟨s0, s1, s2, s3⟩
    let (u, rng) := rng.uniform
    if !decide (floatZero ≤ u) then .error .invalidUniform
    else if !decide (u < floatOne) then .error .invalidUniform
    else
      let (e, rng) := rng.exponential
      if !decide (e < floatInf) then .error .invalidExponential
      else if !decide (floatZero < e) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !decide (elapsed < floatInf) then .error .invalidTime
        else if !decide (floatNegInf < elapsed) then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !decide (floatZero ≤ v) then .error .invalidUniform
          else if !decide (v < floatOne) then .error .invalidUniform
          else
            let k := descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
              Gen11.usize_one_pos (u * total)
            let j := k - P
            let acc :=
              if !decide (j < numRx) then false
              else
                let lower := fget c.lower j
                let threshold := v * fget c.tree k
                if decide (floatZero < lower) && decide (threshold ≤ lower) then true
                else
                  let actual := fget rates j * natToFloat ((aget factors j).eval pop)
                  decide (floatZero < actual) && decide (threshold ≤ actual)
            if acc then
              let time := now + elapsed / total
              if !decide (time < floatInf) then .error .invalidTime
              else if !decide (now < time) then .error .invalidTime
              else if !decide (time ≤ horizon) then
                .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count.toNat, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                  trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
              else if he : evFuel = 0 then .error .eventLimit
              else
                let chs := changesAt C n hval j
                let p := applyTest chs.1 n chs.2 ms c.lo c.hi hms hlo hhi 0 pop hpop false
                if hps : p.size = n then
                  let trace := if save then trace.push (time, ⟨p, c.lo, c.hi⟩) else trace
                  run C codes ms n hms hval numRx P hP2 rates factors horizon save cap (evFuel - 1)
                    cap p hps c hlo hhi time total floatZero rng.s0 rng.s1 rng.s2 rng.s3
                    (count + 1) trace
                else
                  let pop' := p.pop
                  have hpop' : pop'.size = n := by
                    have h2 : p.size = n ∨ p.size = n + 1 :=
                      applyTest_size chs.1 n chs.2 ms c.lo c.hi hms hlo hhi _ 0 rfl pop hpop false
                    simp only [pop', Array.size_pop]
                    omega
                  let c' := chs.1.foldl
                    (fun c ch => Gen16.refresh C.gen5 codes P hP2 ms pop' c ch.species) c
                  have hs := Gen16.foldRefresh_size C.gen5 codes P hP2 ms pop' chs.1 c
                  have hlo' : c'.lo.size = n := by rw [← hlo]; exact hs.1
                  have hhi' : c'.hi.size = n := by rw [← hhi]; exact hs.2
                  let trace := if save then trace.push (time, ⟨pop', c'.lo, c'.hi⟩) else trace
                  let total := fget c'.tree 1
                  if !decide (total < floatInf) then .error (.invalidRate numRx.toNat)
                  else if !decide (floatNegInf < total) then .error (.invalidRate numRx.toNat)
                  else if !decide (floatZero < total) then
                    .ok ⟨⟨pop', c'.lo, c'.hi⟩, horizon, count.toNat + 1,
                      ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩, trace.push (horizon, ⟨pop', c'.lo, c'.hi⟩)⟩
                  else
                    run C codes ms n hms hval numRx P hP2 rates factors horizon save cap
                      (evFuel - 1) cap pop' hpop' c' hlo' hhi' time total floatZero rng.s0 rng.s1
                      rng.s2 rng.s3 (count + 1) trace
            else
              run C codes ms n hms hval numRx P hP2 rates factors horizon save cap evFuel (prFuel - 1)
                pop hpop c hlo hhi now total elapsed rng.s0 rng.s1 rng.s2 rng.s3 count trace
    else
      Gen16.run C codes ms n hms hval C.gen5.base.depth P.toNat numRx.toNat P hP2 rates factors
        horizon save cap.toNat evFuel.toNat prFuel.toNat pop hpop c hlo hhi now total elapsed
        s0 s1 s2 s3 count.toNat trace
termination_by (evFuel.toNat, prFuel.toNat)
decreasing_by
  all_goals first
    | (have : evFuel.toNat ≠ 0 := fun h => he (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat evFuel he]; exact Prod.Lex.left _ _ (by omega))
    | (have : prFuel.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat prFuel hz]; exact Prod.Lex.right _ (by omega))

/-- Generation 16's start, entering generation 17's driver when the network's changes, the
initial brackets and the counts allow it. -/
@[inline] def start (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let total := c.tree.get! 1
  if !Gen7.finite total then .error (.invalidRate C.gen5.base.numRx)
  else if !decide (floatZero < total) then
    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
  else if h : 2 * C.gen5.base.leaves < USize.size then
    if hs : pop.size = C.gen5.base.ms.size ∧ c.lo.size = C.gen5.base.ms.size ∧
        c.hi.size = C.gen5.base.ms.size ∧ Gen15.validChanges C C.gen5.base.ms.size = true ∧
        changesOK C = true ∧ inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
        count + fuel < USize.size ∧ cap < USize.size ∧ C.gen5.base.numRx < USize.size then
      run C codes C.gen5.base.ms C.gen5.base.ms.size rfl (Gen15.validChanges_spec hs.2.2.2.1)
        C.gen5.base.numRx.toUSize C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h)
        C.gen5.base.rates C.gen5.base.factors horizon save cap.toUSize fuel.toUSize cap.toUSize
        pop hs.1 c hs.2.1 hs.2.2.1 now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize
        trace
    else Gen16.start C codes horizon save cap fuel pop c now rng count trace
  else Gen16.start C codes horizon save cap fuel pop c now rng count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(Gen7.finite start && Gen7.finite horizon && decide (start ≤ horizon)) then
    .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen6.compile net
    Gen17.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen17
