import JumpProcessesLean.Proofs.TreeRSSATree
import JumpProcessesLean.Proofs.EndToEnd

/-!
# The bracket model of a mass-action network

A Tree-RSSA state carries populations and brackets. `bracketModel net` is the public
driver model on these states: the propensities are the mass-action propensities of the
populations, the rate bounds are the propensities at the bracket ends, and a transition
fires the reaction and refreshes the stale brackets. Every reachable state satisfies the
bracket invariant, so the bounds are valid and decide absorption.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA

/-! ### Mass-action factors -/

lemma fallingFactorial_pos_iff (n k : Nat) : 0 < fallingFactorial n k ↔ k ≤ n := by
  induction k with
  | zero => simp [fallingFactorial]
  | succ k ih =>
    unfold fallingFactorial
    split_ifs with h
    · simp only [lt_irrefl, false_iff]
      omega
    · have h1 := ih.mpr (by omega)
      exact ⟨fun _ => by omega, fun _ => Nat.mul_pos h1 (by omega)⟩

lemma fallingFactorial_mono {n n' : Nat} (h : n ≤ n') (k : Nat) :
    fallingFactorial n k ≤ fallingFactorial n' k := by
  induction k with
  | zero => simp [fallingFactorial]
  | succ k ih =>
    unfold fallingFactorial
    split_ifs with h1 h2
    · exact le_refl _
    · exact Nat.zero_le _
    · omega
    · exact Nat.mul_le_mul ih (by omega)

lemma combinations_eq (rs : Array (Nat × Nat)) (pop : Array Nat) :
    combinations rs pop = (rs.toList.map fun p => fallingFactorial pop[p.1]! p.2).prod := by
  unfold combinations
  rw [← Array.foldl_toList]
  suffices h : ∀ (l : List (Nat × Nat)) (a : Nat),
      l.foldl (fun acc p => acc * fallingFactorial pop[p.1]! p.2) a =
        a * (l.map fun p => fallingFactorial pop[p.1]! p.2).prod by
    simpa using h rs.toList 1
  intro l
  induction l with
  | nil => intro a; simp
  | cons p l ih =>
    intro a
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, Nat.mul_assoc]

lemma combinations_pos_iff (rs : Array (Nat × Nat)) (pop : Array Nat) :
    0 < combinations rs pop ↔ ∀ p ∈ rs.toList, p.2 ≤ pop[p.1]! := by
  rw [combinations_eq, Nat.pos_iff_ne_zero, Ne, List.prod_eq_zero_iff]
  simp only [List.mem_map, not_exists, not_and]
  constructor
  · intro h p hp
    have := h p hp
    exact (fallingFactorial_pos_iff _ _).mp (Nat.pos_of_ne_zero this)
  · intro h p hp
    exact Nat.pos_iff_ne_zero.mp ((fallingFactorial_pos_iff _ _).mpr (h p hp))

lemma combinations_mono (rs : Array (Nat × Nat)) (pop pop' : Array Nat)
    (h : ∀ p ∈ rs.toList, pop[p.1]! ≤ pop'[p.1]!) :
    combinations rs pop ≤ combinations rs pop' := by
  rw [combinations_eq, combinations_eq]
  have key : ∀ l : List (Nat × Nat), (∀ p ∈ l, pop[p.1]! ≤ pop'[p.1]!) →
      (l.map fun p => fallingFactorial pop[p.1]! p.2).prod ≤
        (l.map fun p => fallingFactorial pop'[p.1]! p.2).prod := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons p l ih =>
      intro hl
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul (fallingFactorial_mono (hl p (by simp)) _)
        (ih fun q hq => hl q (by simp [hq]))
  exact key _ h

lemma propensity_real (rx : Reaction ℝ) (pop : Array Nat) :
    propensity realArithmetic rx pop = rx.rate * (combinations rx.reactants pop : ℝ) := rfl

/-! ### The largest reactant stoichiometry -/

private def msStep (acc : Array Nat) (p : Nat × Nat) : Array Nat :=
  if p.1 < acc.size then acc.set! p.1 (max acc[p.1]! p.2) else acc

private lemma msStep_size (acc : Array Nat) (p : Nat × Nat) : (msStep acc p).size = acc.size := by
  unfold msStep; split <;> simp

private lemma msStep_mono (acc : Array Nat) (p : Nat × Nat) (t : Nat) :
    acc[t]! ≤ (msStep acc p)[t]! := by
  unfold msStep
  split
  · by_cases ht : t = p.1
    · subst ht; rw [Array.getElem!_set!_self _ _ _ (by assumption)]; exact le_max_left _ _
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm ht)]
  · exact le_refl _

private lemma msFold_size (l : List (Nat × Nat)) (acc : Array Nat) :
    (l.foldl msStep acc).size = acc.size := by
  induction l generalizing acc with
  | nil => rfl
  | cons p l ih => rw [List.foldl_cons, ih, msStep_size]

private lemma msFold_mono (l : List (Nat × Nat)) (acc : Array Nat) (t : Nat) :
    acc[t]! ≤ (l.foldl msStep acc)[t]! := by
  induction l generalizing acc with
  | nil => exact le_refl _
  | cons p l ih => exact (msStep_mono acc p t).trans (ih _)

private lemma msFold_ge (l : List (Nat × Nat)) (acc : Array Nat) (p : Nat × Nat) (hp : p ∈ l)
    (hs : p.1 < acc.size) : p.2 ≤ (l.foldl msStep acc)[p.1]! := by
  induction l generalizing acc with
  | nil => simp at hp
  | cons q l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hl
    · refine le_trans ?_ (msFold_mono l _ _)
      unfold msStep
      simp only [hs, ↓reduceIte]
      rw [Array.getElem!_set!_self _ _ _ hs]
      exact le_max_right _ _
    · exact ih _ hl (by rw [msStep_size]; exact hs)

private lemma maxStoich_eq {α : Type} (net : Network α) :
    net.maxStoich = net.reactions.toList.foldl (fun acc rx => rx.reactants.toList.foldl msStep acc)
      (Array.replicate net.numSpecies 0) := by
  unfold Network.maxStoich
  rw [← Array.foldl_toList]
  congr 1
  funext acc rx
  rw [← Array.foldl_toList]
  rfl

lemma maxStoich_size {α : Type} (net : Network α) : net.maxStoich.size = net.numSpecies := by
  rw [maxStoich_eq]
  suffices h : ∀ (l : List (Reaction α)) (acc : Array Nat),
      (l.foldl (fun acc rx => rx.reactants.toList.foldl msStep acc) acc).size = acc.size by
    rw [h]; simp
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons rx l ih => intro acc; rw [List.foldl_cons, ih, msFold_size]

/-- Every reactant stoichiometry is at most the recorded maximum of its species. -/
lemma le_maxStoich {α : Type} (net : Network α) (rx : Reaction α) (hrx : rx ∈ net.reactions.toList)
    (p : Nat × Nat) (hp : p ∈ rx.reactants.toList) (hs : p.1 < net.numSpecies) :
    p.2 ≤ net.maxStoich[p.1]! := by
  rw [maxStoich_eq]
  have hmono : ∀ (l : List (Reaction α)) (acc : Array Nat) (t : Nat),
      acc[t]! ≤ (l.foldl (fun acc rx => rx.reactants.toList.foldl msStep acc) acc)[t]! := by
    intro l
    induction l with
    | nil => intro acc t; exact le_refl _
    | cons r l ih => intro acc t; exact (msFold_mono _ _ _).trans (ih _ _)
  have key : ∀ (l : List (Reaction α)) (acc : Array Nat), rx ∈ l → p.1 < acc.size →
      p.2 ≤ (l.foldl (fun acc rx => rx.reactants.toList.foldl msStep acc) acc)[p.1]! := by
    intro l
    induction l with
    | nil => intro acc h; simp at h
    | cons r l ih =>
      intro acc hmem hsz
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hl
      · exact (msFold_ge _ _ p hp hsz).trans (hmono l _ _)
      · exact ih _ hl (by rw [msFold_size]; exact hsz)
  exact key _ _ hrx (by simpa using hs)

/-! ### Brackets and the invariant -/

lemma bracket_spec (ms n : Nat) :
    (bracket ms n).1 ≤ n ∧ n ≤ (bracket ms n).2 ∧ (n < ms → (bracket ms n).2 = n) := by
  unfold bracket
  split_ifs with h0 h1 h2
  · subst h0; simp
  · simp
  · exact ⟨by omega, by omega, fun h => absurd h h1⟩
  · exact ⟨by omega, by omega, fun h => absurd h h1⟩

/-- The bracket condition of species `s`. -/
def BracketOK (ms : Array Nat) (st : State) (s : Nat) : Prop :=
  st.lo[s]! ≤ st.pop[s]! ∧ st.pop[s]! ≤ st.hi[s]! ∧ (st.pop[s]! < ms[s]! → st.hi[s]! = st.pop[s]!)

/-- Sizes agree and every species satisfies its bracket condition. -/
def BracketInv (ms : Array Nat) (st : State) : Prop :=
  st.lo.size = st.pop.size ∧ st.hi.size = st.pop.size ∧ ∀ s < st.pop.size, BracketOK ms st s

lemma stale_eq_false_iff (ms n lo hi : Nat) :
    stale ms n lo hi = false ↔ (lo ≤ n ∧ n ≤ hi ∧ (n < ms → hi = n)) := by
  unfold stale
  by_cases h1 : n < lo
  · simp only [h1, decide_true, Bool.true_or, Bool.true_eq_false, false_iff, not_and]
    intro h; omega
  by_cases h2 : hi < n
  · simp only [h1, h2, decide_true, decide_false, Bool.false_or, Bool.true_or, Bool.true_eq_false,
      false_iff, not_and]
    intro _ h; omega
  by_cases h3 : n < ms
  · by_cases h4 : hi = n
    · subst h4
      simp [h3]
    · simp only [h1, h2, h3, decide_false, decide_true, Bool.false_or, Bool.true_and]
      constructor
      · intro h; simp [h4] at h
      · intro h; exact absurd (h.2.2 trivial) h4
  · simp only [h1, h2, h3, decide_false, Bool.false_or, Bool.false_and]
    simp only [true_iff]
    exact ⟨by omega, by omega, fun h => h.elim⟩

lemma refreshBracket_pop (ms : Array Nat) (st : State) (s : Nat) :
    (refreshBracket ms st s).pop = st.pop := by
  unfold refreshBracket; split <;> rfl

lemma refreshBracket_lo_size (ms : Array Nat) (st : State) (s : Nat) :
    (refreshBracket ms st s).lo.size = st.lo.size := by
  unfold refreshBracket; split <;> simp

lemma refreshBracket_hi_size (ms : Array Nat) (st : State) (s : Nat) :
    (refreshBracket ms st s).hi.size = st.hi.size := by
  unfold refreshBracket; split <;> simp

/-- A refresh keeps every bracket condition and establishes the refreshed one. -/
lemma refreshBracket_ok (ms : Array Nat) (st : State) (s t : Nat) (hlo : t < st.lo.size)
    (hhi : t < st.hi.size) (h : BracketOK ms st t ∨ t = s) :
    BracketOK ms (refreshBracket ms st s) t := by
  unfold refreshBracket
  split
  · by_cases hts : t = s
    · subst hts
      unfold BracketOK
      simp only
      rw [Array.getElem!_set!_self _ _ _ hlo, Array.getElem!_set!_self _ _ _ hhi]
      exact bracket_spec _ _
    · rcases h with h | h
      · unfold BracketOK at h ⊢
        simp only
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hts),
          Array.getElem!_set!_ne _ _ _ _ (Ne.symm hts)]
        exact h
      · exact absurd h hts
  · rename_i hstale
    rcases h with h | h
    · exact h
    · subst h
      unfold BracketOK
      exact (stale_eq_false_iff _ _ _ _).mp (by simpa using hstale)

/-! ### Firing preserves the invariant -/

lemma applyChange_size (pop : Array Nat) (c : Nat × Int) : (applyChange pop c).size = pop.size := by
  unfold applyChange; simp

lemma foldl_applyChange_size (l : List (Nat × Int)) (pop : Array Nat) :
    (l.foldl applyChange pop).size = pop.size := by
  induction l generalizing pop with
  | nil => rfl
  | cons c l ih => rw [List.foldl_cons, ih, applyChange_size]

lemma foldl_applyChange_get (l : List (Nat × Int)) (pop : Array Nat) (t : Nat)
    (ht : ∀ c ∈ l, c.1 ≠ t) : (l.foldl applyChange pop)[t]! = pop[t]! := by
  induction l generalizing pop with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldl_cons, ih _ (fun c' hc' => ht c' (by simp [hc']))]
    unfold applyChange
    exact Array.getElem!_set!_ne _ _ _ _ (ht c (by simp))

lemma foldl_refresh_shape (ms : Array Nat) (l : List (Nat × Int)) (st : State) :
    (l.foldl (fun st c => refreshBracket ms st c.1) st).pop = st.pop ∧
      (l.foldl (fun st c => refreshBracket ms st c.1) st).lo.size = st.lo.size ∧
      (l.foldl (fun st c => refreshBracket ms st c.1) st).hi.size = st.hi.size := by
  induction l generalizing st with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons c l ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (refreshBracket ms st c.1)
    exact ⟨h1.trans (refreshBracket_pop _ _ _), h2.trans (refreshBracket_lo_size _ _ _),
      h3.trans (refreshBracket_hi_size _ _ _)⟩

lemma foldl_refresh_ok (ms : Array Nat) (l : List (Nat × Int)) (st : State) (t : Nat)
    (hlo : t < st.lo.size) (hhi : t < st.hi.size) (h : BracketOK ms st t ∨ ∃ c ∈ l, c.1 = t) :
    BracketOK ms (l.foldl (fun st c => refreshBracket ms st c.1) st) t := by
  induction l generalizing st with
  | nil =>
    rcases h with h | ⟨c, hc, _⟩
    · exact h
    · simp at hc
  | cons c l ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [refreshBracket_lo_size]; exact hlo
    · rw [refreshBracket_hi_size]; exact hhi
    · rcases h with h | ⟨c', hc', hct⟩
      · exact Or.inl (refreshBracket_ok ms st c.1 t hlo hhi (Or.inl h))
      · rcases List.mem_cons.mp hc' with rfl | hl
        · exact Or.inl (refreshBracket_ok ms st c'.1 t hlo hhi (Or.inr hct.symm))
        · exact Or.inr ⟨c', hl, hct⟩

/-- Firing a reaction preserves the bracket invariant and the population size. -/
theorem fire_inv {α : Type} (net : Network α) (ms : Array Nat) (st : State) (j : Nat)
    (h : BracketInv ms st) :
    BracketInv ms (fire net ms st j) ∧ (fire net ms st j).pop.size = st.pop.size := by
  obtain ⟨hlo, hhi, hok⟩ := h
  unfold fire
  simp only [← Array.foldl_toList]
  set ch := (changesOf net j).toList
  set st1 : State := { st with pop := ch.foldl applyChange st.pop }
  have hpop1 : st1.pop.size = st.pop.size := foldl_applyChange_size _ _
  obtain ⟨hp, hl, hh⟩ := foldl_refresh_shape ms ch st1
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hl, hp, hpop1]; exact hlo
  · rw [hh, hp, hpop1]; exact hhi
  · intro t ht
    rw [hp, hpop1] at ht
    apply foldl_refresh_ok
    · show t < st.lo.size; omega
    · show t < st.hi.size; omega
    · by_cases hmem : ∃ c ∈ ch, c.1 = t
      · exact Or.inr hmem
      · left
        have hne : ∀ c ∈ ch, c.1 ≠ t := fun c hc hct => hmem ⟨c, hc, hct⟩
        have hget : st1.pop[t]! = st.pop[t]! := foldl_applyChange_get ch st.pop t hne
        have hold := hok t ht
        unfold BracketOK at hold ⊢
        rw [hget]
        exact hold
  · rw [hp, hpop1]

/-! ### The bracket model -/

/-- In-range species and nonnegative rate constants. -/
structure ValidNetwork (net : Network ℝ) : Prop where
  wellFormed : net.WellFormed
  nonneg : ∀ rx ∈ net.reactions.toList, 0 ≤ rx.rate

/-- States whose bracket bounds are certified. -/
def Bracketed (net : Network ℝ) (st : State) : Prop :=
  BracketInv net.maxStoich st ∧ st.pop.size = net.numSpecies

lemma fire_bracketed (net : Network ℝ) (st : State) (j : Nat) (h : Bracketed net st) :
    Bracketed net (fire net net.maxStoich st j) :=
  ⟨(fire_inv net _ st j h.1).1, (fire_inv net _ st j h.1).2.trans h.2⟩

open Classical in
/-- The public driver model of Tree-RSSA states: mass-action propensities of the
populations, bounds at the bracket ends, and bracket-refreshing transitions. -/
noncomputable def bracketModel (net : Network ℝ) : Model ℝ State where
  rates st := net.reactions.map (propensity realArithmetic · st.pop)
  bounds st := if Bracketed net st then
      ⟨lowerBounds realArithmetic net st, upperBounds realArithmetic net st⟩
    else ⟨net.reactions.map (propensity realArithmetic · st.pop),
      net.reactions.map (propensity realArithmetic · st.pop)⟩
  transition st j := .ok (fire net net.maxStoich st j)

lemma propensity_nonneg (net : Network ℝ) (hv : ValidNetwork net) (rx : Reaction ℝ)
    (hrx : rx ∈ net.reactions.toList) (pop : Array Nat) : 0 ≤ propensity realArithmetic rx pop := by
  rw [propensity_real]
  exact mul_nonneg (hv.nonneg rx hrx) (Nat.cast_nonneg _)

lemma propensity_bracket (net : Network ℝ) (hv : ValidNetwork net) (st : State)
    (hb : Bracketed net st) (rx : Reaction ℝ) (hrx : rx ∈ net.reactions.toList) :
    propensity realArithmetic rx st.lo ≤ propensity realArithmetic rx st.pop ∧
      propensity realArithmetic rx st.pop ≤ propensity realArithmetic rx st.hi := by
  have hr := hv.nonneg rx hrx
  have hreact := (hv.wellFormed.2 rx hrx).1
  have hok : ∀ p ∈ rx.reactants.toList, BracketOK net.maxStoich st p.1 := fun p hp =>
    hb.1.2.2 p.1 (by rw [hb.2]; exact hreact p hp)
  rw [propensity_real, propensity_real, propensity_real]
  exact ⟨mul_le_mul_of_nonneg_left (by exact_mod_cast combinations_mono _ _ _ fun p hp => (hok p hp).1) hr,
    mul_le_mul_of_nonneg_left (by exact_mod_cast combinations_mono _ _ _ fun p hp => (hok p hp).2.1) hr⟩

/-- On bracketed states some reaction is enabled iff the upper bounds have a positive
total: exact brackets below the largest stoichiometry rule out spurious upper bounds. -/
theorem enabled_iff_upper_pos (net : Network ℝ) (hv : ValidNetwork net) (st : State)
    (hb : Bracketed net st) :
    (∃ rx ∈ net.reactions.toList, 0 < propensity realArithmetic rx st.pop) ↔
      0 < (upperBounds realArithmetic net st).toList.sum := by
  have hup : ∀ x ∈ (upperBounds realArithmetic net st).toList, 0 ≤ x := by
    intro x hx
    simp only [TreeRSSA.upperBounds, Array.toList_map, List.mem_map] at hx
    obtain ⟨rx, hrx, rfl⟩ := hx
    exact propensity_nonneg net hv rx hrx _
  constructor
  · rintro ⟨rx, hrx, hpos⟩
    have hmem : propensity realArithmetic rx st.hi ∈ (upperBounds realArithmetic net st).toList := by
      simp only [TreeRSSA.upperBounds, Array.toList_map, List.mem_map]
      exact ⟨rx, hrx, rfl⟩
    exact lt_of_lt_of_le (lt_of_lt_of_le hpos (propensity_bracket net hv st hb rx hrx).2)
      (List.single_le_sum hup _ hmem)
  · intro hsum
    by_contra hnone
    simp only [not_exists, not_and, not_lt] at hnone
    have hzero : ∀ x ∈ (upperBounds realArithmetic net st).toList, x ≤ 0 := by
      intro x hx
      simp only [TreeRSSA.upperBounds, Array.toList_map, List.mem_map] at hx
      obtain ⟨rx, hrx, rfl⟩ := hx
      by_contra hpos
      simp only [not_le] at hpos
      -- a positive upper bound forces every reactant into its enabled range
      have hr : 0 < rx.rate := by
        rw [propensity_real] at hpos
        by_contra hr
        have : rx.rate = 0 := le_antisymm (not_lt.mp hr) (hv.nonneg rx hrx)
        rw [this, zero_mul] at hpos
        exact lt_irrefl _ hpos
      have hcomb : 0 < combinations rx.reactants st.hi := by
        rw [propensity_real] at hpos
        exact_mod_cast pos_of_mul_pos_right hpos hr.le
      have henabled : 0 < combinations rx.reactants st.pop := by
        rw [combinations_pos_iff] at hcomb ⊢
        intro q hq
        have hs : q.1 < net.numSpecies := (hv.wellFormed.2 rx hrx).1 q hq
        have hok := hb.1.2.2 q.1 (by rw [hb.2]; exact hs)
        by_contra hlt
        simp only [not_le] at hlt
        have hms : q.2 ≤ net.maxStoich[q.1]! := le_maxStoich net rx hrx q hq hs
        have hhi := hok.2.2 (by omega)
        have := hcomb q hq
        omega
      have := hnone rx hrx
      rw [propensity_real] at this
      have hpos' : 0 < rx.rate * (combinations rx.reactants st.pop : ℝ) :=
        mul_pos hr (by exact_mod_cast henabled)
      linarith
    have : (TreeRSSA.upperBounds realArithmetic net st).toList.sum ≤ 0 := by
      simpa using (List.sum_le_sum (l := (TreeRSSA.upperBounds realArithmetic net st).toList)
        (f := id) (g := fun _ => (0 : ℝ)) hzero)
    linarith

end JumpProcessesLean.Proofs
