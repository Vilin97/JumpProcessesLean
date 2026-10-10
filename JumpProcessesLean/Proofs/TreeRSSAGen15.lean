import JumpProcessesLean.Proofs.TreeRSSAGen14
import JumpProcessesLean.TreeRSSA.Gen15

/-!
# Generation 15 is generation 14, hence the specification

The machine-word loop over a reaction's changes, with every change fewer than `USize.size`,
visits the changes in order, and setting an entry in range is `set!`, so it computes the fold of
`Change.apply` (`applyFrom_val`). When the reading loop finds no changed species out of its
bracket, every refresh of generation 13's fold leaves the cache unchanged (`anyStale_false`,
`foldRefresh_id`). So generation 15's firing returns generation 13's populations and cache
(`fire15_eq`), and its driver is generation 14's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

lemma validChanges_small {C : Gen6.Compiled} {n : Nat} (h : Gen15.validChanges C n = true)
    (j : Nat) : (C.changes[j]!).size < USize.size := by
  unfold Gen15.validChanges at h
  rw [Array.all_eq_true] at h
  by_cases hj : j < C.changes.size
  · have := ((Bool.and_eq_true _ _).mp (h j hj)).1
    simp only [decide_eq_true_eq] at this
    rw [getElem!_pos C.changes j hj]; exact this
  · rw [getElem!_neg C.changes j hj]
    show 0 < USize.size
    exact USize.size_pos

lemma usize_toNat_eq {α : Type} (a : Array α) (h : a.size < USize.size) :
    a.usize.toNat = a.size := by
  simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' h]

lemma apply_set (pop : Array Nat) (ch : Gen6.Change) (hs : ch.species < pop.size) :
    pop.set ch.species (pop[ch.species] + ch.up - ch.down) hs = Gen6.Change.apply pop ch := by
  simp only [Gen6.Change.apply, getElem!_pos pop ch.species hs, Array.set!_eq_setIfInBounds,
    Array.setIfInBounds_def, hs, ↓reduceDIte]

theorem applyFrom_val (chs : Array Gen6.Change) (n : Nat)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (hsmall : chs.size < USize.size) :
    ∀ i pop hp, (Gen15.applyFrom chs n hv i pop hp).val =
      (chs.toList.drop i.toNat).foldl Gen6.Change.apply pop := by
  intro i pop hp
  induction i, pop, hp using Gen15.applyFrom.induct chs n hv with
  | case1 i pop hp h hi ch hs ih =>
    rw [Gen15.applyFrom, dite_eq_left_of_eq_true (eq_true h)]
    simp only []
    rw [ih, Gen15.succ_toNat_of_lt_usize chs i h]
    conv_rhs => rw [List.drop_eq_getElem_cons (by simp; exact hi), List.foldl_cons]
    rw [Array.getElem_toList]
    congr 1
    exact apply_set pop _ _
  | case2 i pop hp h =>
    rw [Gen15.applyFrom, dite_eq_right_iff.mpr (fun h' => absurd h' h)]
    have : chs.size ≤ i.toNat := by
      have h1 : ¬ i.toNat < chs.usize.toNat := h
      rw [usize_toNat_eq chs hsmall] at h1; omega
    rw [List.drop_eq_nil_of_le (by simp; exact this)]
    rfl

theorem anyStale_false (chs : Array Gen6.Change) (n : Nat)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (ms pop lo hi : Array Nat)
    (hms : ms.size = n) (hp : pop.size = n) (hlo : lo.size = n) (hhi : hi.size = n)
    (hsmall : chs.size < USize.size) :
    ∀ m i, chs.size - i.toNat = m → Gen15.anyStale chs n hv ms pop lo hi hms hp hlo hhi i = false →
      ∀ ch ∈ chs.toList.drop i.toNat,
        Gen9.staleI ms[ch.species]! pop[ch.species]! lo[ch.species]! hi[ch.species]! = false := by
  intro m
  induction m with
  | zero =>
    intro i hm _ ch hch
    rw [List.drop_eq_nil_of_le (by simp; omega)] at hch
    exact absurd hch List.not_mem_nil
  | succ m ih =>
    intro i hm hf ch hch
    rw [Gen15.anyStale] at hf
    split at hf
    · rename_i h
      have hi' := Gen15.lt_size_of_lt_usize chs i h
      dsimp only at hf
      split at hf
      · exact absurd hf (by decide)
      · rename_i hst
        rw [List.drop_eq_getElem_cons (by simp; exact hi'), List.mem_cons] at hch
        rcases hch with rfl | hch
        · have hsn := hv _ hi'
          rw [Array.getElem_toList, getElem!_pos ms _ (by rw [hms]; exact hsn),
            getElem!_pos pop _ (by rw [hp]; exact hsn), getElem!_pos lo _ (by rw [hlo]; exact hsn),
            getElem!_pos hi _ (by rw [hhi]; exact hsn)]
          simpa using hst
        · have := ih (i + 1) (by rw [Gen15.succ_toNat_of_lt_usize chs i h]; omega) hf ch
          rw [Gen15.succ_toNat_of_lt_usize chs i h] at this
          exact this hch
    · rename_i h
      have : chs.size ≤ i.toNat := by
        have h1 : ¬ i.toNat < chs.usize.toNat := h
        rw [usize_toNat_eq chs hsmall] at h1; omega
      rw [List.drop_eq_nil_of_le (by simp; exact this)] at hch
      exact absurd hch List.not_mem_nil

theorem foldRefresh_id (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms pop : Array Nat) (L : List Gen6.Change) (c : Cache)
    (h : ∀ ch ∈ L,
      Gen9.staleI ms[ch.species]! pop[ch.species]! c.lo[ch.species]! c.hi[ch.species]! = false) :
    L.foldl (fun c ch => Gen13.refresh C codes P hP2 ms pop c ch.species) c = c := by
  induction L with
  | nil => rfl
  | cons ch L ih =>
    simp only [List.foldl_cons]
    have h0 := h ch (List.mem_cons_self ..)
    have : Gen13.refresh C codes P hP2 ms pop c ch.species = c := by
      simp only [Gen13.refresh, h0, Bool.false_eq_true, ↓reduceIte]
    rw [this]
    exact ih (fun ch' hch' => h ch' (List.mem_cons_of_mem _ hch'))

theorem fire15_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms : Array Nat) (n : Nat) (hms : ms.size = n)
    (hval : Gen15.ValidChanges C n) (hsmall : ∀ j : Nat, (C.changes[j]!).size < USize.size)
    (pop : Array Nat) (hpop : pop.size = n) (c : Cache) (hlo : c.lo.size = n)
    (hhi : c.hi.size = n) (j : Nat) :
    (Gen15.fire C codes P hP2 ms n hms hval pop hpop c hlo hhi j).val =
      Gen13.fire C codes P hP2 ms pop c j := by
  unfold Gen15.fire Gen13.fire
  have hv := applyFrom_val (C.changes[j]!) n (hval j) (hsmall j) 0 pop hpop
  simp only [USize.toNat_zero, List.drop_zero, Array.foldl_toList] at hv
  dsimp only
  split
  · rename_i hst
    simp only [hv]
  · rename_i hst
    simp only [hv]
    congr 1
    rw [← Array.foldl_toList]
    symm
    apply foldRefresh_id
    have := anyStale_false (C.changes[j]!) n (hval j) ms _ c.lo c.hi hms
      (Gen15.applyFrom (C.changes[j]!) n (hval j) 0 pop hpop).property hlo hhi (hsmall j) _ 0 rfl
      (by simpa using hst)
    simpa [hv] using this

theorem descendW15_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (depth : Nat) (hPd : P.toNat = 2 ^ depth) :
    ∀ n i (k : USize) (hk0 : 0 < k.toNat) (x : Float), i + n = depth → 2 ^ i ≤ k.toNat →
      k.toNat < 2 ^ (i + 1) →
      (Gen15.descendW tree P hP hP2 k hk0 x).toNat = Gen1.descend tree n k.toNat x := by
  intro n
  induction n with
  | zero =>
    intro i k hk0 x hi hlo _
    obtain rfl : i = depth := by omega
    have hkP : ¬ k < P := by
      intro h
      have : k.toNat < P.toNat := h
      omega
    rw [Gen15.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
    rfl
  | succ n ih =>
    intro i k hk0 x hi hlo hhi
    have hpow : 2 ^ (i + 1) ≤ 2 ^ depth := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hkP' : k.toNat < P.toNat := by omega
    have hkP : k < P := hkP'
    have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
    have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
    have hs1 : 2 ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
    have hs0 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ]; omega
    rw [Gen15.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
    simp only [Gen1.descend, floatArray_uget_eq, h2]
    split
    · rw [← h2]
      exact ih (i + 1) (2 * k) _ x (by omega) (by rw [h2]; omega) (by rw [h2]; omega)
    · rw [show 2 * k.toNat + 1 = (2 * k + 1).toNat from h21.symm]
      exact ih (i + 1) (2 * k + 1) _ _ (by omega) (by rw [h21]; omega) (by rw [h21]; omega)


theorem fire15_mk (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms : Array Nat) (n : Nat) (hms : ms.size = n)
    (hval : Gen15.ValidChanges C n) (hsmall : ∀ j : Nat, (C.changes[j]!).size < USize.size)
    (pop : Array Nat) (hpop : pop.size = n) (c : Cache) (hlo : c.lo.size = n)
    (hhi : c.hi.size = n) (j : Nat) :
    Gen15.fire C codes P hP2 ms n hms hval pop hpop c hlo hhi j =
      ⟨((Gen13.fire C codes P hP2 ms pop c j).1, (Gen13.fire C codes P hP2 ms pop c j).2),
        ⟨by rw [← fire15_eq C codes P hP2 ms n hms hval hsmall pop hpop c hlo hhi j]
            exact (Gen15.fire C codes P hP2 ms n hms hval pop hpop c hlo hhi j).property.1,
         by rw [← fire15_eq C codes P hP2 ms n hms hval hsmall pop hpop c hlo hhi j]
            exact (Gen15.fire C codes P hP2 ms n hms hval pop hpop c hlo hhi j).property.2.1,
         by rw [← fire15_eq C codes P hP2 ms n hms hval hsmall pop hpop c hlo hhi j]
            exact (Gen15.fire C codes P hP2 ms n hms hval pop hpop c hlo hhi j).property.2.2⟩⟩ := by
  apply Subtype.ext
  show (Gen15.fire C codes P hP2 ms n hms hval pop hpop c hlo hhi j).val =
    ((Gen13.fire C codes P hP2 ms pop c j).1, (Gen13.fire C codes P hP2 ms pop c j).2)
  rw [fire15_eq C codes P hP2 ms n hms hval hsmall]

/-- Generation 15's driver from one proposal on is generation 14's, given the statement for
the next event. -/
theorem run15_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (n : Nat)
    (hms : C.gen5.base.ms.size = n) (hval : Gen15.ValidChanges C n)
    (hsmall : ∀ j : Nat, (C.changes[j]!).size < USize.size) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float)
    (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count
      trace,
      Gen15.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel
          pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace =
        Gen14.run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P
          hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace,
      Gen15.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel
          pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace =
        Gen14.run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P
          hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace
    rw [Gen15.run.eq_1, Gen14.run.eq_1]
  | succ pf ih =>
    intro pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace
    rw [Gen15.run.eq_2]
    by_cases hT : 2 * P ≤ c.tree.usize
    · rw [dite_eq_left_of_eq_true (eq_true hT), Gen14.run.eq_2,
        dite_eq_left_of_eq_true (eq_true hT)]
      have h1 : (1 : USize).toNat = 1 := by
        rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
      have hd15 : ∀ x, (Gen15.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
          Gen11.usize_one_pos x).toNat = Gen1.descend c.tree C.gen5.base.depth 1 x := by
        intro x
        rw [descendW15_eq c.tree P _ hP2 C.gen5.base.depth hPd C.gen5.base.depth 0 1 _ x
          (by omega) (by rw [h1]; simp) (by rw [h1]; simp), h1]
      have hd14 : ∀ x, (Gen14.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
          Gen11.usize_one_pos x).toNat = Gen1.descend c.tree C.gen5.base.depth 1 x := by
        intro x
        rw [descendW14_eq c.tree P _ hP2 C.gen5.base.depth hPd C.gen5.base.depth 0 1 _ x
          (by omega) (by rw [h1]; simp) (by rw [h1]; simp), h1]
      simp only [hd15, hd14, ih, fire15_mk C codes P hP2 _ n hms hval hsmall]
      cases fuel with
      | zero => rfl
      | succ f =>
        simp only [hnext f rfl]
    · rw [dite_eq_right_iff.mpr (fun h => absurd h hT)]

theorem gen15_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (n : Nat)
    (hms : C.gen5.base.ms.size = n) (hval : Gen15.ValidChanges C n)
    (hsmall : ∀ j : Nat, (C.changes[j]!).size < USize.size) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ C.gen5.base.depth) (horizon : Float)
    (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace,
      Gen15.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel
          pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace =
        Gen14.run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx P
          hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total
          elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run15_eq_of C codes n hms hval hsmall P hP2 hPd horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    exact run15_eq_of C codes n hms hval hsmall P hP2 hPd horizon save cap (f + 1)
      (fun f' h => by cases h; exact ih)

theorem start15_eq (C : Gen6.Compiled) (codes : Array (Array Nat))
    (hC : C.gen5.base.leaves = 2 ^ C.gen5.base.depth) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) :
    Gen15.start C codes horizon save cap fuel pop c now rng count trace =
      Gen14.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen15.start Gen14.start
  split
  · rename_i h
    have hPd : C.gen5.base.leaves.toUSize.toNat = 2 ^ C.gen5.base.depth := by
      rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega), hC]
    split
    · rename_i hs
      simp only [gen15_run_eq C codes _ rfl _ (validChanges_small hs.2.2.2) _ _ hPd]
    · rfl
  · rfl

/-- Generation 15 returns what generation 14 returns, on every network and input. -/
theorem gen15_eq_gen14 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen15.simulate net initial start horizon rng maxEvents save cap =
      Gen14.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen15.simulate Gen14.simulate
  simp only [start15_eq _ _ (gen6_compile_leaves net)]

/-- **Generation 15 is the specification.** For every network whose reactant species are in
range and every input, generation 15 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen15_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen15.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen15_eq_gen14, gen14_simulate_eq net hwf]

end JumpProcessesLean.Proofs
