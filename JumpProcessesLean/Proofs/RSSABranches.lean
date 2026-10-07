import JumpProcessesLean.Proofs.OperationalRSSA
import JumpProcessesLean.Proofs.OperationalNRM

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma checkBoundsAux_real (rates lower upper : List ℝ)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (index : Nat) : checkBoundsAux realArithmetic rates lower upper index = .ok () := by
  induction rates generalizing lower upper index with
  | nil =>
    have hl : lower = [] := List.length_eq_zero_iff.mp (by simpa using hshape.1)
    have hu : upper = [] := List.length_eq_zero_iff.mp (by simpa using hshape.2)
    subst lower; subst upper; rfl
  | cons a rates ih =>
    cases lower with
    | nil => simp at hshape
    | cons lo lower =>
      cases upper with
      | nil => simp at hshape
      | cons up upper =>
        have h0 := hb 0 (by simp)
        simp only [List.getElem_cons_zero] at h0
        have hUp : 0 ≤ up := (h0.1.trans h0.2.1).trans h0.2.2
        have hs : lower.length = rates.length ∧ upper.length = rates.length := by simpa using hshape
        have ht : ∀ (i : Nat) (hi : i < rates.length),
            0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega) := by
          intro i hi
          have hi' : i + 1 < (a :: rates).length := by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hi
          have hh := hb (i + 1) hi'
          rw [List.getElem_cons_succ a rates i hi'] at hh
          simpa only [List.getElem_cons_succ] using hh
        simp only [checkBoundsAux, validRate, realArithmetic, Bool.true_and, h0.1, hUp,
          h0.2.1, h0.2.2, decide_true, Bool.and_self, ite_true]
        exact ih lower upper hs ht (index + 1)

theorem checkBounds_real (rates : Array ℝ) (bounds : RateBounds ℝ)
    (hshape : bounds.lower.size = rates.size ∧ bounds.upper.size = rates.size)
    (hb : ∀ (i : Nat) (hi : i < rates.size),
      0 ≤ bounds.lower[i]'(by omega) ∧ bounds.lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ bounds.upper[i]'(by omega)) :
    checkBounds realArithmetic rates bounds = .ok () := by
  have hr : ∀ a ∈ rates.toList, 0 ≤ a := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact (hb i (by simpa using hi)).1.trans (hb i (by simpa using hi)).2.1
  unfold checkBounds
  rw [checkRates_real rates hr]
  simp only [Bind.bind, Except.bind, hshape.1, hshape.2, bne_self_eq_false, Bool.or_self,
    Bool.false_eq_true, ite_false]
  exact checkBoundsAux_real rates.toList bounds.lower.toList bounds.upper.toList
    (by simpa using hshape) (by intro i hi; simpa using hb i (by simpa using hi)) 0

theorem rssa_real_calls_proposals (rates : Array ℝ) (bounds : RateBounds ℝ)
    (hshape : bounds.lower.size = rates.size ∧ bounds.upper.size = rates.size)
    (hb : ∀ (i : Nat) (hi : i < rates.size),
      0 ≤ bounds.lower[i]'(by omega) ∧ bounds.lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ bounds.upper[i]'(by omega))
    (hA : 0 < rates.toList.sum) (hB : 0 < bounds.upper.toList.sum)
    (now : ℝ) (rng : Tape ℝ) (fuel : Nat) :
    rssa realArithmetic (tapeSource ℝ) rates bounds now rng fuel =
      rssaProposals realArithmetic (tapeSource ℝ) rates bounds now bounds.upper.toList.sum fuel 0 rng := by
  have hany : rates.any (realArithmetic.lt realArithmetic.zero) = true := by
    apply Array.any_eq_true.mpr
    have hex : ∃ (i : Nat) (hi : i < rates.size), 0 < rates[i] := by
      by_contra h
      have hn : ∀ a ∈ rates.toList, a ≤ 0 := by
        intro a ha
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
        exact le_of_not_gt (fun hp => h ⟨i, by simpa using hi, hp⟩)
      have hsum : rates.toList.sum ≤ 0 := by
        simpa using (List.sum_le_sum (l := rates.toList) (f := id) (g := fun _ => (0 : ℝ)) hn)
      exact (not_le.mpr hA) hsum
    obtain ⟨i, hi, hp⟩ := hex
    exact ⟨i, hi, by simpa only [realArithmetic, decide_eq_true_eq] using hp⟩
  unfold rssa
  rw [checkBounds_real rates bounds hshape hb]
  simp only [Bind.bind, Except.bind]
  rw [sumRates_real, hany]
  simp only [realArithmetic, Bool.not_true, Bool.false_eq_true, ite_false, hB, decide_true]


noncomputable def proposalAcceptMark (rates lower upper : List ℝ) (p : Option Nat × ℝ) : Option Nat :=
  match p.1 with
  | none => none
  | some i => if rssaAccept realArithmetic lower[i]! rates[i]! (p.2 * upper[i]!) then some i else none

noncomputable def proposalMark (rates lower upper : List ℝ) (p : ℝ × ℝ) : Option Nat :=
  proposalAcceptMark rates lower upper (selection upper p.1, p.2)

lemma measurable_proposalMark (rates lower upper : List ℝ) :
    Measurable (proposalMark rates lower upper) := by
  have hm : Measurable (proposalAcceptMark rates lower upper) := by
    apply measurable_from_prod_countable_right
    intro o
    cases o with
    | none => exact measurable_const
    | some i =>
      unfold proposalAcceptMark
      apply Measurable.ite _ measurable_const measurable_const
      simp only [rssaAccept, realArithmetic, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      measurability
  exact hm.comp (((measurable_chooseAux _ _ _).comp (measurable_fst.mul_const _)).prodMk measurable_snd)

lemma proposalMark_some_iff (rates lower upper : List ℝ) (p : ℝ × ℝ) (i : Nat) :
    proposalMark rates lower upper p = some i ↔ selection upper p.1 = some i ∧
      rssaAccept realArithmetic lower[i]! rates[i]! (p.2 * upper[i]!) = true := by
  unfold proposalMark proposalAcceptMark
  cases h : selection upper p.1 with
  | none => simp
  | some j =>
    by_cases ha : rssaAccept realArithmetic lower[j]! rates[j]! (p.2 * upper[j]!) = true
    · simp only [ha, ite_true, Option.some.injEq]
      constructor
      · intro hji; subst j; exact ⟨rfl, ha⟩
      · intro hi; exact hi.1
    · simp only [ha, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff, Option.some.injEq]
      rintro ⟨rfl, hi⟩
      exact ha hi

lemma chooseAux_some_bounds (weights : List ℝ) (x c : ℝ) (k j : Nat)
    (h : chooseAux realArithmetic x weights c k = some j) : k ≤ j ∧ j < k + weights.length := by
  induction weights generalizing c k with
  | nil => simp [chooseAux] at h
  | cons a rest ih =>
    simp only [chooseAux] at h
    split at h
    · cases h; simp
    · obtain ⟨hl, hu⟩ := ih _ _ h
      simp only [List.length_cons]
      omega

lemma proposalMark_some_bound (rates lower upper : List ℝ) (p : ℝ × ℝ) (i : Nat)
    (h : proposalMark rates lower upper p = some i) : i < upper.length := by
  have hs := (proposalMark_some_iff rates lower upper p i).mp h
  have hb := chooseAux_some_bounds upper (p.1 * upper.sum) 0 0 i hs.1
  simpa using hb.2

theorem proposalMark_probability (rates lower upper : List ℝ)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (hB : 0 < upper.sum) (i : Nat) (hi : i < rates.length) :
    (unitUniform.prod unitUniform) (proposalMark rates lower upper ⁻¹' {some i}) =
      ENNReal.ofReal (rates[i] / upper.sum) := by
  have he : proposalMark rates lower upper ⁻¹' {some i} =
      {p : ℝ × ℝ | selection upper p.1 = some i ∧
        rssaAccept realArithmetic (lower[i]'(by omega)) rates[i] (p.2 * upper[i]'(by omega)) = true} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, proposalMark_some_iff, mem_setOf_eq]
    simp [getElem!_pos, hi, show i < lower.length by omega,
      show i < upper.length by omega]
  rw [he]
  exact rssa_proposal_probability rates lower upper hshape hb hB i hi

theorem proposalMark_rejection_probability (rates lower upper : List ℝ)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (hA : 0 < rates.sum) :
    (unitUniform.prod unitUniform) (proposalMark rates lower upper ⁻¹' {none}) =
      ENNReal.ofReal (1 - rates.sum / upper.sum) := by
  have hr : ∀ a ∈ rates, 0 ≤ a := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact (hb i hi).1.trans (hb i hi).2.1
  have hAB : rates.sum ≤ upper.sum := by
    have hu : List.ofFn (fun i : Fin rates.length => upper[i.val]'(by omega)) = upper := by
      apply List.ext_getElem (by simp [hshape.2])
      intro i hi hiu
      simp
    calc
      rates.sum = ∑ i : Fin rates.length, rates[i.val] := by
        simpa only [List.ofFn_getElem] using (List.sum_ofFn (f := fun i : Fin rates.length => rates[i.val]))
      _ ≤ ∑ i : Fin rates.length, upper[i.val]'(by omega) :=
        Finset.sum_le_sum (fun i _ => (hb i.val i.isLt).2.2)
      _ = upper.sum := by rw [← List.sum_ofFn, hu]
  have hB := hA.trans_le hAB
  let f (i : Nat) := proposalMark rates lower upper ⁻¹' {some i}
  have hm (i : Nat) : MeasurableSet (f i) := (measurable_proposalMark _ _ _) (measurableSet_singleton _)
  have hd : (↑(Finset.range rates.length) : Set Nat).PairwiseDisjoint f := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    exact hij (Option.some.inj (hpi.symm.trans hpj))
  have hset : proposalMark rates lower upper ⁻¹' {none} =
      (⋃ i ∈ Finset.range rates.length, f i)ᶜ := by
    ext p
    cases h : proposalMark rates lower upper p with
    | none => simp [f, h]
    | some i =>
      have hi : i < rates.length := by have := proposalMark_some_bound rates lower upper p i h; omega
      simp [f, h, hi]
  rw [hset, measure_compl ((Finset.range rates.length).measurableSet_biUnion (fun i _ => hm i))
    (measure_ne_top _ _),
    measure_biUnion_finset hd (fun i _ => hm i)]
  have hs : (∑ i ∈ Finset.range rates.length, (unitUniform.prod unitUniform) (f i)) =
      ENNReal.ofReal (rates.sum / upper.sum) := by
    calc
      _ = ∑ i ∈ Finset.range rates.length, ENNReal.ofReal (rates[i]! / upper.sum) := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa [getElem!_pos, Finset.mem_range.mp hi] using
          proposalMark_probability rates lower upper hshape hb hB i (Finset.mem_range.mp hi)
      _ = ENNReal.ofReal (rates.sum / upper.sum) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          rw [← Finset.sum_div]
          congr 1
          rw [Finset.sum_range, ← List.sum_ofFn]
          simp only [getElem!_pos, Fin.isLt, List.ofFn_getElem]
        · intro i hi
          simpa [getElem!_pos, Finset.mem_range.mp hi] using
            div_nonneg (hr _ (List.getElem_mem (Finset.mem_range.mp hi))) hB.le
  rw [hs, measure_univ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (div_nonneg hA.le hB.le)]

/-- Convolution is connected to the finite-vector sum, rather than stipulated as its law. -/
theorem exponential_vector_sum_law (B : ℝ) (hB : 0 < B) (n : Nat) :
    (Measure.pi (fun _ : Fin n => expMeasure B)).map (fun c => ∑ i, c i) =
      sumExponentialLaw B n := by
  let : IsProbabilityMeasure (expMeasure B) := isProbabilityMeasure_expMeasure hB
  induction n with
  | zero =>
    simp only [Fin.sum_univ_zero, sumExponentialLaw]
    rw [Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hpres := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => expMeasure B) 0
    have heq : (Measure.pi (fun _ : Fin (n + 1) => expMeasure B)).map (fun c => ∑ i, c i) =
        ((expMeasure B).prod (Measure.pi (fun _ : Fin n => expMeasure B))).map
          (fun p => p.1 + ∑ i, p.2 i) := by
      rw [← hpres.map_eq, Measure.map_map (by fun_prop) e.measurable]
      congr 1
      funext c
      simpa [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply,
        Fin.insertNthEquiv, Fin.removeNth, Fin.tail] using (Fin.sum_univ_succAbove c 0)
    rw [heq, sumExponentialLaw, ← ih]
    unfold Measure.conv
    have hc := Measure.map_prod_map (expMeasure B) (Measure.pi (fun _ : Fin n => expMeasure B))
      (f := id) (g := fun c => ∑ i, c i) measurable_id (by fun_prop)
    simp only [Measure.map_id] at hc
    rw [hc, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

theorem uniform_clock_sum_law (B : ℝ) (hB : 0 < B) (n : Nat) :
    (Measure.pi (fun _ : Fin n => unitUniform)).map
      (fun u => ∑ i, exponentialClock B (u i)) = sumExponentialLaw B n := by
  have hm : Measurable (fun u : Fin n → ℝ => fun i => exponentialClock B (u i)) :=
    Measurable.of_eval (fun i => (measurable_exponentialClock B).comp (measurable_pi_apply i))
  rw [← exponential_vector_sum_law B hB n, ← race_uniform_input_law (fun _ => B) (fun _ => hB),
    Measure.map_map (by fun_prop) hm]
  rfl

lemma rssa_step_real (rates : Array ℝ) (bounds : RateBounds ℝ) (now elapsed e u v : ℝ)
    (hB : 0 < bounds.upper.toList.sum) (hz : 0 ≤ elapsed) (he : 0 < e)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) (j fuel : Nat)
    (hj : selection bounds.upper.toList u = some j) (us es : List ℝ) :
    rssaProposals realArithmetic (tapeSource ℝ) rates bounds now bounds.upper.toList.sum
      (fuel + 1) elapsed ⟨u :: v :: us, e :: es⟩ =
    if rssaAccept realArithmetic bounds.lower[j]! rates[j]! (v * bounds.upper[j]!) then
      .ok (some ⟨now + (elapsed + e) / bounds.upper.toList.sum, j⟩, ⟨us, es⟩)
    else rssaProposals realArithmetic (tapeSource ℝ) rates bounds now bounds.upper.toList.sum
      fuel (elapsed + e) ⟨us, es⟩ := by
  have hdU : drawUniform realArithmetic (tapeSource ℝ) (⟨u :: v :: us, e :: es⟩ : Tape ℝ) =
      .ok (u, ⟨v :: us, e :: es⟩) := by
    simp [drawUniform, tapeSource, realArithmetic, Bind.bind, Except.bind, hu.1.le, hu.2]
    rfl
  have hdE : drawExponential realArithmetic (tapeSource ℝ) (⟨v :: us, e :: es⟩ : Tape ℝ) =
      .ok (e, ⟨v :: us, es⟩) := by
    simp [drawExponential, tapeSource, realArithmetic, Bind.bind, Except.bind, he]
    rfl
  have hdV : drawUniform realArithmetic (tapeSource ℝ) (⟨v :: us, es⟩ : Tape ℝ) =
      .ok (v, ⟨us, es⟩) := by
    simp [drawUniform, tapeSource, realArithmetic, Bind.bind, Except.bind, hv.1.le, hv.2]
    rfl
  have hsel : weightedIndex realArithmetic bounds.upper
      (realArithmetic.mul u bounds.upper.toList.sum) = .ok j := by
    unfold weightedIndex
    change (match selection bounds.upper.toList u with | some i => Except.ok i | none => Except.error Error.selectionFailure) = _
    rw [hj]
  have ht : now < now + (elapsed + e) / bounds.upper.toList.sum := by
    have hp : 0 < elapsed + e := by linarith
    exact lt_add_of_pos_right _ (div_pos hp hB)
  rw [rssaProposals, hdU]
  simp only [Bind.bind, Except.bind]
  rw [hsel]
  simp only [Except.bind]
  rw [hdE]
  simp only [Except.bind, show realArithmetic.finite (realArithmetic.add elapsed e) = true by rfl,
    Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hdV]
  simp only [Except.bind, realArithmetic, ht, decide_true, Bool.true_and,
    Bool.not_true, Bool.false_eq_true, ite_false, Pure.pure, Except.pure]

abbrev ProposalInput := ℝ × (ℝ × ℝ)
noncomputable def proposalUniforms (xs : List ProposalInput) : List ℝ :=
  xs.flatMap (fun p => [p.2.1, p.2.2])
noncomputable def proposalExponentials (xs : List ProposalInput) : List ℝ := xs.map (fun p => -log p.1)
def GoodProposal (p : ProposalInput) : Prop := p.1 ∈ Ioo 0 1 ∧ p.2.1 ∈ Ioo 0 1 ∧ p.2.2 ∈ Ioo 0 1

/-- Actual RSSA execution on every finite first-success branch, including consumed tapes. -/
theorem rssa_first_success_executes (rates : Array ℝ) (bounds : RateBounds ℝ)
    (huppers : ∀ a ∈ bounds.upper.toList, 0 ≤ a) (hB : 0 < bounds.upper.toList.sum)
    (rejected : List ProposalInput) (last : ProposalInput) (i : Nat)
    (hg : ∀ p ∈ rejected ++ [last], GoodProposal p)
    (hr : ∀ p ∈ rejected, proposalMark rates.toList bounds.lower.toList bounds.upper.toList p.2 = none)
    (hi : proposalMark rates.toList bounds.lower.toList bounds.upper.toList last.2 = some i)
    (now elapsed : ℝ) (hz : 0 ≤ elapsed) :
    rssaProposals realArithmetic (tapeSource ℝ) rates bounds now bounds.upper.toList.sum
      (rejected.length + 1) elapsed
      ⟨proposalUniforms (rejected ++ [last]), proposalExponentials (rejected ++ [last])⟩ =
      .ok (some ⟨now + (elapsed + (proposalExponentials (rejected ++ [last])).sum) /
        bounds.upper.toList.sum, i⟩, ⟨[], []⟩) := by
  induction rejected generalizing elapsed with
  | nil =>
    have hg0 := hg last (by simp)
    obtain ⟨hsel, hacc⟩ := (proposalMark_some_iff _ _ _ last.2 i).mp hi
    have ha : rssaAccept realArithmetic bounds.lower[i]! rates[i]!
      (last.2.2 * bounds.upper[i]!) = true := by simpa only [Array.getElem!_toList] using hacc
    have hs := rssa_step_real rates bounds now elapsed (-log last.1) last.2.1 last.2.2 hB hz
      (neg_pos.mpr (log_neg hg0.1.1 hg0.1.2)) hg0.2.1 hg0.2.2 i 0 hsel [] []
    simpa [proposalUniforms, proposalExponentials, ha] using hs
  | cons p rest ih =>
    have hp := hg p (by simp)
    have hrest : ∀ q ∈ rest ++ [last], GoodProposal q := fun q hq => hg q (by simp [hq])
    have hreject := hr p (by simp)
    obtain ⟨j, hj⟩ := chooseAux_exists bounds.upper.toList huppers
      (p.2.1 * bounds.upper.toList.sum) 0 (by nlinarith [hp.2.1.1])
      (by nlinarith [hp.2.1.2]) 0
    have he : 0 < -log p.1 := neg_pos.mpr (log_neg hp.1.1 hp.1.2)
    have ha : rssaAccept realArithmetic bounds.lower[j]! rates[j]!
        (p.2.2 * bounds.upper[j]!) = false := by
      have hs : selection bounds.upper.toList p.2.1 = some j := hj
      simp only [proposalMark, proposalAcceptMark, hs, Array.getElem!_toList] at hreject
      by_cases ha : rssaAccept realArithmetic bounds.lower[j]! rates[j]!
          (p.2.2 * bounds.upper[j]!) = true
      · simp [ha] at hreject
      · exact Bool.eq_false_of_not_eq_true ha
    have hs := rssa_step_real rates bounds now elapsed (-log p.1) p.2.1 p.2.2 hB hz he
      hp.2.1 hp.2.2 j (rest.length + 1) hj
      (proposalUniforms (rest ++ [last])) (proposalExponentials (rest ++ [last]))
    simp only [ha, Bool.false_eq_true, ite_false] at hs
    have hi' := ih hrest (fun q hq => hr q (by simp [hq])) (elapsed + -log p.1) (by linarith)
    simp only [List.cons_append, proposalUniforms, List.flatMap_cons, List.append_assoc,
      List.cons_append, List.nil_append, proposalExponentials, List.map_cons,
      List.length_cons, List.sum_cons] at hs hi' ⊢
    rw [show rest.length + 1 + 1 = (rest.length + 1) + 1 by omega, hs]
    simpa only [add_assoc] using hi'

noncomputable def proposalBranch (rates lower upper : List ℝ) (k i : Nat) :
    Set (Fin (k + 1) → ℝ × ℝ) :=
  univ.pi (fun j => proposalMark rates lower upper ⁻¹' {if j.val < k then none else some i})

lemma measurable_proposalBranch (rates lower upper : List ℝ) (k i : Nat) :
    MeasurableSet (proposalBranch rates lower upper k i) := by
  exact MeasurableSet.univ_pi (fun j => (measurable_proposalMark _ _ _) (measurableSet_singleton _))

/-- The mark probability of the first successful proposal is derived from the selector
and acceptance comparison on every independent primitive input. -/
theorem proposalBranch_probability (rates lower upper : List ℝ)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (hA : 0 < rates.sum) (hB : 0 < upper.sum) (k i : Nat) (hi : i < rates.length) :
    (Measure.pi (fun _ : Fin (k + 1) => unitUniform.prod unitUniform))
      (proposalBranch rates lower upper k i) =
      ENNReal.ofReal ((1 - rates.sum / upper.sum) ^ k * (rates[i] / upper.sum)) := by
  have hq : 0 ≤ 1 - rates.sum / upper.sum := by
      have hprob := proposalMark_rejection_probability rates lower upper hshape hb hA
      have hAB : rates.sum ≤ upper.sum := by
        have hu : List.ofFn (fun j : Fin rates.length => upper[j.val]'(by omega)) = upper := by
          apply List.ext_getElem (by simp [hshape.2]); intro j hj hju; simp
        calc
          rates.sum = ∑ j : Fin rates.length, rates[j.val] := by
            simpa only [List.ofFn_getElem] using (List.sum_ofFn (f := fun j : Fin rates.length => rates[j.val]))
          _ ≤ ∑ j : Fin rates.length, upper[j.val]'(by omega) := Finset.sum_le_sum (fun j _ => (hb j.val j.isLt).2.2)
          _ = upper.sum := by rw [← List.sum_ofFn, hu]
      exact sub_nonneg.mpr ((div_le_one hB).mpr hAB)
  rw [proposalBranch, Measure.pi_pi, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.isLt, ite_true, Fin.val_last, lt_self_iff_false, ite_false]
  simp_rw [proposalMark_rejection_probability rates lower upper hshape hb hA]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    proposalMark_probability rates lower upper hshape hb hB i hi,
    ← ENNReal.ofReal_pow hq, ← ENNReal.ofReal_mul (pow_nonneg hq k)]

/-- Pushforward of the actual independent primitive-input measure, restricted to a
first-success branch. `rssa_first_success_executes` identifies its time with the code. -/
noncomputable def rssaExecutableBranchLaw (rates lower upper : List ℝ) (k i : Nat) : Measure ℝ :=
  (((Measure.pi (fun _ : Fin (k + 1) => unitUniform)).prod
    (Measure.pi (fun _ : Fin (k + 1) => unitUniform.prod unitUniform))).restrict
      (univ ×ˢ proposalBranch rates lower upper k i)).map
        (fun p => ∑ j, exponentialClock upper.sum (p.1 j))

theorem rssa_executable_branch_law (rates lower upper : List ℝ)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (hA : 0 < rates.sum) (hB : 0 < upper.sum) (k i : Nat) (hi : i < rates.length) :
    rssaExecutableBranchLaw rates lower upper k i =
      ENNReal.ofReal ((1 - rates.sum / upper.sum) ^ k * (rates[i] / upper.sum)) •
        sumExponentialLaw upper.sum (k + 1) := by
  have hf : Measurable (fun p : (Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ × ℝ) =>
      ∑ j, exponentialClock upper.sum (p.1 j)) := by unfold exponentialClock; fun_prop
  ext s hs
  rw [rssaExecutableBranchLaw, Measure.map_apply hf hs, Measure.restrict_apply (hf hs)]
  have he : (fun p : (Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ × ℝ) =>
      ∑ j, exponentialClock upper.sum (p.1 j)) ⁻¹' s ∩
      (univ ×ˢ proposalBranch rates lower upper k i) =
      ((fun u : Fin (k + 1) → ℝ => ∑ j, exponentialClock upper.sum (u j)) ⁻¹' s) ×ˢ
        proposalBranch rates lower upper k i := by ext p; simp
  rw [he, Measure.prod_prod, proposalBranch_probability rates lower upper hshape hb hA hB k i hi,
    ← Measure.map_apply (by unfold exponentialClock; fun_prop) hs, uniform_clock_sum_law _ hB,
    Measure.smul_apply, smul_eq_mul, mul_comm]

noncomputable def rssaExecutableLaw (rates lower upper : List ℝ) (i : Nat) : Measure ℝ :=
  Measure.sum (fun k : Nat => rssaExecutableBranchLaw rates lower upper k i)

theorem rssa_executable_clock_law (rates lower upper : List ℝ)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (hA : 0 < rates.sum) (hB : 0 < upper.sum) (hAB : rates.sum ≤ upper.sum)
    (i : Nat) (hi : i < rates.length) :
    rssaExecutableLaw rates lower upper i = ENNReal.ofReal (rates[i] / rates.sum) • expMeasure rates.sum := by
  unfold rssaExecutableLaw
  simp_rw [rssa_executable_branch_law rates lower upper hshape hb hA hB _ i hi]
  change infiniteRejectionClockLaw upper.sum (1 - rates.sum / upper.sum) (rates[i] / upper.sum) = _
  have hq0 : 0 ≤ 1 - rates.sum / upper.sum := sub_nonneg.mpr ((div_le_one hB).mpr hAB)
  have hq1 : 1 - rates.sum / upper.sum < 1 := by linarith [div_pos hA hB]
  rw [infinite_rejection_clock_law _ _ _ hB hq0 hq1
    (div_nonneg ((hb i hi).1.trans (hb i hi).2.1) hB.le)]
  congr 2 <;> field_simp [hA.ne', hB.ne'] <;> ring

/-- The finite uniform vectors underlying a measured branch run the actual proposal loop. -/
theorem rssa_uniform_branch_executes (rates : Array ℝ) (bounds : RateBounds ℝ)
    (huppers : ∀ a ∈ bounds.upper.toList, 0 ≤ a) (hB : 0 < bounds.upper.toList.sum)
    (k i : Nat) (u : Fin (k + 1) → ℝ) (v : Fin (k + 1) → ℝ × ℝ)
    (hu : ∀ j, u j ∈ Ioo 0 1)
    (hv : ∀ j, (v j).1 ∈ Ioo 0 1 ∧ (v j).2 ∈ Ioo 0 1)
    (hbranch : v ∈ proposalBranch rates.toList bounds.lower.toList bounds.upper.toList k i) :
    rssaProposals realArithmetic (tapeSource ℝ) rates bounds 0 bounds.upper.toList.sum (k + 1) 0
      ⟨proposalUniforms (List.ofFn (fun j => (u j, v j))),
        proposalExponentials (List.ofFn (fun j => (u j, v j)))⟩ =
      .ok (some ⟨∑ j, exponentialClock bounds.upper.toList.sum (u j), i⟩, ⟨[], []⟩) := by
  let samples : Fin (k + 1) → ProposalInput := fun j => (u j, v j)
  let rejected : List ProposalInput := List.ofFn (fun j : Fin k => samples j.castSucc)
  have hlist : rejected ++ [samples (Fin.last k)] = List.ofFn samples :=
    List.ofFn_succ_last.symm
  have hgood : ∀ p ∈ rejected ++ [samples (Fin.last k)], GoodProposal p := by
    rw [hlist]
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨hu j, hv j⟩
  have hrejected : ∀ p ∈ rejected,
      proposalMark rates.toList bounds.lower.toList bounds.upper.toList p.2 = none := by
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    have h := (mem_pi.mp hbranch) j.castSucc (mem_univ _)
    simpa [Fin.isLt] using h
  have hlast : proposalMark rates.toList bounds.lower.toList bounds.upper.toList
      (samples (Fin.last k)).2 = some i := by
    have h := (mem_pi.mp hbranch) (Fin.last k) (mem_univ _)
    simpa using h
  have hex := rssa_first_success_executes rates bounds huppers hB rejected (samples (Fin.last k))
    i hgood hrejected hlast 0 0 (le_refl 0)
  rw [hlist] at hex
  simp only [rejected, List.length_ofFn, zero_add] at hex
  have hsum : (proposalExponentials (List.ofFn samples)).sum / bounds.upper.toList.sum =
      ∑ j, exponentialClock bounds.upper.toList.sum (u j) := by
    simp only [proposalExponentials, List.map_ofFn, Function.comp_def, List.sum_ofFn, samples,
      exponentialClock, Finset.sum_div]
  simpa only [hsum] using hex

noncomputable def rssaRawBranchTime (rates lower upper : List ℝ) (k : Nat)
    (p : (Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ × ℝ)) : ℝ :=
  match rssaProposals realArithmetic (tapeSource ℝ) rates.toArray ⟨lower.toArray, upper.toArray⟩ 0 upper.sum
      (k + 1) 0 ⟨proposalUniforms (List.ofFn (fun j => (p.1 j, p.2 j))),
        proposalExponentials (List.ofFn (fun j => (p.1 j, p.2 j)))⟩ with
  | .ok (some e, _) => e.time
  | _ => 0

/-- Direct pushforward of the executable RSSA return time on a first-success branch. -/
noncomputable def rssaRawBranchLaw (rates lower upper : List ℝ) (k i : Nat) : Measure ℝ :=
  (((Measure.pi (fun _ : Fin (k + 1) => unitUniform)).prod
    (Measure.pi (fun _ : Fin (k + 1) => unitUniform.prod unitUniform))).restrict
      (univ ×ˢ proposalBranch rates lower upper k i)).map (rssaRawBranchTime rates lower upper k)

theorem rssa_raw_branch_refines (rates lower upper : List ℝ)
    (huppers : ∀ a ∈ upper, 0 ≤ a) (hB : 0 < upper.sum) (k i : Nat) :
    rssaRawBranchLaw rates lower upper k i = rssaExecutableBranchLaw rates lower upper k i := by
  unfold rssaRawBranchLaw rssaExecutableBranchLaw
  apply Measure.map_congr
  have hp : ∀ᵐ p : (Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ × ℝ)
      ∂(Measure.pi (fun _ => unitUniform)).prod (Measure.pi (fun _ => unitUniform.prod unitUniform)),
      (∀ j, p.1 j ∈ Ioo 0 1) ∧ (∀ j, (p.2 j).1 ∈ Ioo 0 1 ∧ (p.2 j).2 ∈ Ioo 0 1) := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [unitUniform_vector_ae_mem (k + 1)] with u hu
    have hmarks : ∀ᵐ v : Fin (k + 1) → ℝ × ℝ ∂Measure.pi (fun _ => unitUniform.prod unitUniform),
        ∀ j, (v j).1 ∈ Ioo 0 1 ∧ (v j).2 ∈ Ioo 0 1 := by
      rw [ae_all_iff]
      intro j
      exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (k + 1) => unitUniform.prod unitUniform)
        (i := j)).eventually unitUniform_pair_ae_mem
    exact hmarks.mono (fun v hv => ⟨hu, hv⟩)
  filter_upwards [ae_restrict_of_ae hp,
    ae_restrict_mem (MeasurableSet.prod MeasurableSet.univ (measurable_proposalBranch rates lower upper k i))] with p hp hbranch
  have hex := rssa_uniform_branch_executes rates.toArray ⟨lower.toArray, upper.toArray⟩
    (by simpa using huppers) (by simpa using hB) k i p.1 p.2 hp.1 hp.2 (by simpa using hbranch.2)
  simp only [List.toList_toArray] at hex
  unfold rssaRawBranchTime
  rw [hex]

noncomputable def rssaValidatedBranchTime (rates lower upper : List ℝ) (k : Nat)
    (p : (Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ × ℝ)) : ℝ :=
  match rssa realArithmetic (tapeSource ℝ) rates.toArray ⟨lower.toArray, upper.toArray⟩ 0
      ⟨proposalUniforms (List.ofFn (fun j => (p.1 j, p.2 j))),
        proposalExponentials (List.ofFn (fun j => (p.1 j, p.2 j)))⟩ (k + 1) with
  | .ok (some e, _) => e.time
  | _ => 0

noncomputable def rssaValidatedBranchLaw (rates lower upper : List ℝ) (k i : Nat) : Measure ℝ :=
  (((Measure.pi (fun _ : Fin (k + 1) => unitUniform)).prod
    (Measure.pi (fun _ : Fin (k + 1) => unitUniform.prod unitUniform))).restrict
      (univ ×ˢ proposalBranch rates lower upper k i)).map (rssaValidatedBranchTime rates lower upper k)

/-- The completely validated wrapper and recursive proposal execution have the derived
exponential-clock mixture law. No density of the executable output is assumed. -/
theorem rssa_validated_executable_law (rates lower upper : List ℝ)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (hA : 0 < rates.sum) (hB : 0 < upper.sum) (hAB : rates.sum ≤ upper.sum)
    (i : Nat) (hi : i < rates.length) :
    Measure.sum (fun k : Nat => rssaValidatedBranchLaw rates lower upper k i) =
      ENNReal.ofReal (rates[i] / rates.sum) • expMeasure rates.sum := by
  have huppers : ∀ a ∈ upper, 0 ≤ a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hjr : j < rates.length := by omega
    exact ((hb j hjr).1.trans (hb j hjr).2.1).trans (hb j hjr).2.2
  have htime (k : Nat) : rssaValidatedBranchTime rates lower upper k = rssaRawBranchTime rates lower upper k := by
    funext p
    unfold rssaValidatedBranchTime rssaRawBranchTime
    rw [rssa_real_calls_proposals rates.toArray ⟨lower.toArray, upper.toArray⟩
      (by simpa using hshape) (by intro j hj; simpa using hb j (by simpa using hj))
      (by simpa using hA) (by simpa using hB)]
  have hbranch (k : Nat) : rssaValidatedBranchLaw rates lower upper k i =
      rssaExecutableBranchLaw rates lower upper k i := by
    unfold rssaValidatedBranchLaw
    rw [htime]
    exact rssa_raw_branch_refines rates lower upper huppers hB k i
  simp_rw [hbranch]
  exact rssa_executable_clock_law rates lower upper hshape hb hA hB hAB i hi

/-- In real arithmetic, a complete valid proposal tape hits the cap exactly when all
its proposals reject. Finite cap errors are not interpreted as absorbing states. -/
theorem rssa_cap_error_iff (rates : Array ℝ) (bounds : RateBounds ℝ)
    (huppers : ∀ a ∈ bounds.upper.toList, 0 ≤ a) (hB : 0 < bounds.upper.toList.sum)
    (samples : List ProposalInput) (hg : ∀ p ∈ samples, GoodProposal p)
    (now elapsed : ℝ) (hz : 0 ≤ elapsed) :
    (rssaProposals realArithmetic (tapeSource ℝ) rates bounds now bounds.upper.toList.sum samples.length elapsed
      ⟨proposalUniforms samples, proposalExponentials samples⟩ = .error .proposalLimit) ↔
    ∀ p ∈ samples, proposalMark rates.toList bounds.lower.toList bounds.upper.toList p.2 = none := by
  induction samples generalizing elapsed with
  | nil => simp [rssaProposals]
  | cons p rest ih =>
    have hp := hg p (by simp)
    have hrest : ∀ q ∈ rest, GoodProposal q := fun q hq => hg q (by simp [hq])
    obtain ⟨j, hj⟩ := chooseAux_exists bounds.upper.toList huppers
      (p.2.1 * bounds.upper.toList.sum) 0 (by nlinarith [hp.2.1.1]) (by nlinarith [hp.2.1.2]) 0
    have he : 0 < -log p.1 := neg_pos.mpr (log_neg hp.1.1 hp.1.2)
    have hmark : proposalMark rates.toList bounds.lower.toList bounds.upper.toList p.2 = none ↔
        rssaAccept realArithmetic bounds.lower[j]! rates[j]! (p.2.2 * bounds.upper[j]!) = false := by
      have hs : selection bounds.upper.toList p.2.1 = some j := hj
      simp only [proposalMark, proposalAcceptMark, hs, Array.getElem!_toList]
      cases ha : rssaAccept realArithmetic bounds.lower[j]! rates[j]! (p.2.2 * bounds.upper[j]!) <;> simp
    have hs := rssa_step_real rates bounds now elapsed (-log p.1) p.2.1 p.2.2 hB hz he
      hp.2.1 hp.2.2 j rest.length hj (proposalUniforms rest) (proposalExponentials rest)
    simp only [proposalUniforms, proposalExponentials, List.flatMap_cons, List.map_cons,
      List.cons_append, List.nil_append, List.length_cons] at hs ⊢
    rw [hs]
    cases ha : rssaAccept realArithmetic bounds.lower[j]! rates[j]! (p.2.2 * bounds.upper[j]!) with
    | false =>
      have hm : proposalMark rates.toList bounds.lower.toList bounds.upper.toList p.2 = none := hmark.mpr ha
      have htail := ih hrest (elapsed + -log p.1) (by linarith)
      simpa [ha, hm, proposalUniforms, proposalExponentials] using htail
    | true =>
      have hm : proposalMark rates.toList bounds.lower.toList bounds.upper.toList p.2 ≠ none := by
        intro h; have := hmark.mp h; rw [ha] at this; contradiction
      simp [ha, hm]

noncomputable def rssaCapRun (rates lower upper : List ℝ) (fuel : Nat)
    (p : (Fin fuel → ℝ) × (Fin fuel → ℝ × ℝ)) : Except Error (Option (Event ℝ) × Tape ℝ) :=
  rssa realArithmetic (tapeSource ℝ) rates.toArray ⟨lower.toArray, upper.toArray⟩ 0
    ⟨proposalUniforms (List.ofFn (fun j => (p.1 j, p.2 j))),
      proposalExponentials (List.ofFn (fun j => (p.1 j, p.2 j)))⟩ fuel

theorem rssa_cap_failure_probability (rates lower upper : List ℝ)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (hA : 0 < rates.sum) (hB : 0 < upper.sum) (hq : 0 ≤ 1 - rates.sum / upper.sum) (fuel : Nat) :
    ((Measure.pi (fun _ : Fin fuel => unitUniform)).prod
      (Measure.pi (fun _ : Fin fuel => unitUniform.prod unitUniform)))
      {p | rssaCapRun rates lower upper fuel p = .error .proposalLimit} =
      ENNReal.ofReal ((1 - rates.sum / upper.sum) ^ fuel) := by
  have huppers : ∀ a ∈ upper, 0 ≤ a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hjr : j < rates.length := by omega
    exact ((hb j hjr).1.trans (hb j hjr).2.1).trans (hb j hjr).2.2
  let rejected : Set (Fin fuel → ℝ × ℝ) :=
    univ.pi (fun _ => proposalMark rates lower upper ⁻¹' {none})
  have hae : {p : (Fin fuel → ℝ) × (Fin fuel → ℝ × ℝ) |
      rssaCapRun rates lower upper fuel p = .error .proposalLimit} =ᵐ[
        (Measure.pi (fun _ => unitUniform)).prod (Measure.pi (fun _ => unitUniform.prod unitUniform))]
        univ ×ˢ rejected := by
    have hp : ∀ᵐ p : (Fin fuel → ℝ) × (Fin fuel → ℝ × ℝ)
        ∂(Measure.pi (fun _ => unitUniform)).prod (Measure.pi (fun _ => unitUniform.prod unitUniform)),
        (∀ j, p.1 j ∈ Ioo 0 1) ∧ (∀ j, (p.2 j).1 ∈ Ioo 0 1 ∧ (p.2 j).2 ∈ Ioo 0 1) := by
      rw [Measure.ae_prod_iff_ae_ae (by measurability)]
      filter_upwards [unitUniform_vector_ae_mem fuel] with u hu
      have hm : ∀ᵐ v : Fin fuel → ℝ × ℝ ∂Measure.pi (fun _ => unitUniform.prod unitUniform),
          ∀ j, (v j).1 ∈ Ioo 0 1 ∧ (v j).2 ∈ Ioo 0 1 := by
        rw [ae_all_iff]
        intro j
        exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin fuel => unitUniform.prod unitUniform)
          (i := j)).eventually unitUniform_pair_ae_mem
      exact hm.mono (fun v hv => ⟨hu, hv⟩)
    filter_upwards [hp] with p hp
    apply propext
    have hg : ∀ s ∈ List.ofFn (fun j : Fin fuel => (p.1 j, p.2 j)), GoodProposal s := by
      intro s hs; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs; exact ⟨hp.1 j, hp.2 j⟩
    have hrun := rssa_cap_error_iff rates.toArray ⟨lower.toArray, upper.toArray⟩
      (by simpa using huppers) (by simpa using hB) (List.ofFn (fun j : Fin fuel => (p.1 j, p.2 j))) hg 0 0 (le_refl 0)
    unfold rssaCapRun
    rw [rssa_real_calls_proposals rates.toArray ⟨lower.toArray, upper.toArray⟩
      (by simpa using hshape) (by intro j hj; simpa using hb j (by simpa using hj))
      (by simpa using hA) (by simpa using hB)]
    simpa [rejected, Set.mem_pi, List.mem_ofFn] using hrun
  rw [measure_congr hae, Measure.prod_prod, measure_univ, one_mul]
  dsimp only [rejected]
  rw [Measure.pi_pi]
  simp_rw [proposalMark_rejection_probability rates lower upper hshape hb hA]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hq]

end JumpProcessesLean.Proofs
