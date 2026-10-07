import JumpProcessesLean.Direct
import JumpProcessesLean.Proofs.Selection
import JumpProcessesLean.Proofs.ExponentialTransform
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import JumpProcessesLean.Proofs.Race

namespace JumpProcessesLean.Proofs
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

instance : MeasurableSpace (Option Nat) := ⊤
instance : DiscreteMeasurableSpace (Option Nat) := ⟨fun _ => trivial⟩

lemma checkRatesAux_real (rates : List ℝ) (hr : ∀ a ∈ rates, 0 ≤ a) (i : Nat) :
    checkRatesAux realArithmetic rates i = .ok () := by
  induction rates generalizing i with
  | nil => rfl
  | cons a rest ih =>
    simp only [checkRatesAux, validRate, realArithmetic, Bool.true_and,
      decide_eq_true (hr a (by simp)), ite_true]
    exact ih (fun b hb => hr b (by simp [hb])) (i + 1)

lemma checkRates_real (rates : Array ℝ) (hr : ∀ a ∈ rates.toList, 0 ≤ a) :
    checkRates realArithmetic rates = .ok () := checkRatesAux_real _ hr 0

lemma sumRates_real (rates : Array ℝ) : sumRates realArithmetic rates = rates.toList.sum := by
  simp only [sumRates, realArithmetic, ← Array.foldl_toList, ← List.sum_eq_foldl]

lemma chooseAux_eq_some_iff (weights : List ℝ) (hn : ∀ a ∈ weights, 0 ≤ a)
    (x cumulative : ℝ) (hx : cumulative ≤ x) (index i : Nat) :
    chooseAux realArithmetic x weights cumulative index = some (index + i) ↔
      i < weights.length ∧ cumulative + (weights.take i).sum ≤ x ∧
        x < cumulative + (weights.take (i + 1)).sum := by
  induction weights generalizing cumulative index i with
  | nil => simp [chooseAux]
  | cons a rest ih =>
    have ha := hn a (by simp)
    have hr : ∀ b ∈ rest, 0 ≤ b := fun b hb => hn b (by simp [hb])
    by_cases h : 0 < a ∧ x < cumulative + a
    · cases i with
      | zero => simp [chooseAux, realArithmetic, h.1, h.2, hx]
      | succ i =>
        have hs : 0 ≤ (rest.take i).sum := List.sum_nonneg (fun b hb => hr b (List.mem_of_mem_take hb))
        have hl : ¬ cumulative + (a + (rest.take i).sum) ≤ x := by linarith
        simp [chooseAux, realArithmetic, h.1, h.2, List.take_succ_cons, hl]
    · have hx' : cumulative + a ≤ x := by
        by_cases hp : 0 < a
        · exact le_of_not_gt (fun hh => h ⟨hp, hh⟩)
        · have : a = 0 := le_antisymm (le_of_not_gt hp) ha
          simpa [this] using hx
      have hc : ¬ (realArithmetic.lt 0 a && realArithmetic.lt x (cumulative + a)) = true := by
        simpa [realArithmetic] using h
      cases i with
      | zero =>
        have hl : ¬ x < cumulative + a := not_lt.mpr hx'
        have hne : chooseAux realArithmetic x rest (cumulative + a) (index + 1) ≠ some index := by
          have hg : ∀ (l : List ℝ) (c : ℝ) (k : Nat),
              (∀ j, chooseAux realArithmetic x l c k = some j → k ≤ j) := by
            intro l
            induction l with
            | nil => simp [chooseAux]
            | cons b bs ih =>
              intro c k j hj
              simp only [chooseAux] at hj
              split at hj
              · cases hj; exact le_refl _
              · exact (Nat.le_succ k).trans (ih _ _ _ hj)
          intro he
          have := hg rest _ _ index he
          omega
        simp only [chooseAux, realArithmetic, ← Bool.decide_and, h, decide_false, Bool.false_eq_true, ite_false, List.take_zero, List.take_succ_cons, List.sum_cons, List.sum_nil, add_zero, hl, and_false, Bool.and_false]
        change (chooseAux realArithmetic x rest (cumulative + a) (index + 1) = some index ↔ False)
        exact iff_false_intro hne
      | succ i =>
        simp only [chooseAux, realArithmetic, ← Bool.decide_and, h, decide_false,
          Bool.false_eq_true, ite_false, List.length_cons, List.take_succ_cons, List.sum_cons]
        change (chooseAux realArithmetic x rest (cumulative + a) (index + 1) = some (index + (i + 1)) ↔ _)
        rw [show index + (i + 1) = index + 1 + i by omega,
          ih hr (cumulative + a) hx' (index + 1) i]
        simp only [Nat.succ_lt_succ_iff, add_assoc]

lemma chooseAux_exists (weights : List ℝ) (hn : ∀ a ∈ weights, 0 ≤ a)
    (x cumulative : ℝ) (hl : cumulative ≤ x) (hu : x < cumulative + weights.sum)
    (index : Nat) : ∃ i, chooseAux realArithmetic x weights cumulative index = some i := by
  induction weights generalizing cumulative index with
  | nil => simp at hu; linarith
  | cons a rest ih =>
    by_cases h : 0 < a ∧ x < cumulative + a
    · exact ⟨index, by simp [chooseAux, realArithmetic, h.1, h.2]⟩
    · have hr : ∀ b ∈ rest, 0 ≤ b := fun b hb => hn b (by simp [hb])
      have hx : cumulative + a ≤ x := by
        have ha := hn a (by simp)
        by_cases hp : 0 < a
        · exact le_of_not_gt (fun hh => h ⟨hp, hh⟩)
        · have : a = 0 := le_antisymm (le_of_not_gt hp) ha
          simpa [this] using hl
      obtain ⟨i, hi⟩ := ih hr (cumulative + a) hx (by simpa [add_assoc] using hu) (index + 1)
      exact ⟨i, by simpa [chooseAux, realArithmetic, ← Bool.decide_and, h] using hi⟩

lemma measurable_chooseAux (weights : List ℝ) (c : ℝ) (index : Nat) :
    Measurable (fun x => chooseAux realArithmetic x weights c index) := by
  induction weights generalizing c index with
  | nil => exact measurable_const
  | cons a rest ih =>
    simp only [chooseAux, realArithmetic, ← Bool.decide_and, decide_eq_true_eq]
    exact Measurable.ite (by measurability) measurable_const (ih _ _)

noncomputable def selection (weights : List ℝ) (u : ℝ) : Option Nat :=
  chooseAux realArithmetic (u * weights.sum) weights 0 0

lemma selection_interval (weights : List ℝ) (hn : ∀ a ∈ weights, 0 ≤ a)
    (hA : 0 < weights.sum) (i : Nat) (hi : i < weights.length) :
    selection weights ⁻¹' {some i} ∩ Ioo 0 1 =
      Ico ((weights.take i).sum / weights.sum)
        ((weights.take (i + 1)).sum / weights.sum) ∩ Ioo 0 1 := by
  ext u
  by_cases hu : u ∈ Ioo 0 1
  · simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, hu, and_true,
      selection]
    rw [← Nat.zero_add i]
    rw [chooseAux_eq_some_iff weights hn _ 0 (by nlinarith [hu.1]) 0 i]
    simp only [hi, true_and, zero_add, mem_Ico]
    exact and_congr (by rw [div_le_iff₀ hA])
      (by rw [lt_div_iff₀ hA])
  · simp [hu]

/-- The categorical probability is derived from the actual cumulative selector. -/
theorem selection_probability (weights : List ℝ) (hn : ∀ a ∈ weights, 0 ≤ a)
    (hA : 0 < weights.sum) (i : Nat) (hi : i < weights.length) :
    unitUniform (selection weights ⁻¹' {some i}) = ENNReal.ofReal (weights[i] / weights.sum) := by
  have hm : Measurable (selection weights) :=
    (measurable_chooseAux _ _ _).comp (measurable_id.mul_const _)
  rw [unitUniform, Measure.restrict_apply (hm (measurableSet_singleton _)),
    selection_interval weights hn hA i hi]
  have h0 : 0 ≤ (weights.take i).sum / weights.sum :=
    div_nonneg (List.sum_nonneg (fun a ha => hn a (List.mem_of_mem_take ha))) hA.le
  have h1 : (weights.take (i + 1)).sum / weights.sum ≤ 1 := by
    apply (div_le_one hA).mpr
    have hd : 0 ≤ (weights.drop (i + 1)).sum := List.sum_nonneg (fun a ha => hn a (List.mem_of_mem_drop ha))
    have hs : (weights.take (i + 1)).sum + (weights.drop (i + 1)).sum = weights.sum := by
      rw [← List.sum_append, List.take_append_drop]
    linarith
  have hae : Ico ((weights.take i).sum / weights.sum)
      ((weights.take (i + 1)).sum / weights.sum) ∩ Ioo 0 1 =ᵐ[volume]
      Ico ((weights.take i).sum / weights.sum)
        ((weights.take (i + 1)).sum / weights.sum) := by
    have hz : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [hz] with u hu
    apply propext
    simp only [mem_inter_iff, mem_Ico, mem_Ioo]
    constructor
    · exact And.left
    · intro h
      exact ⟨h, lt_of_le_of_ne (h0.trans h.1) (Ne.symm hu), h.2.trans_le h1⟩
  rw [measure_congr hae, Real.volume_Ico, List.sum_take_succ weights i hi]
  congr 1
  ring

/-- Pointwise execution refinement, including validation and both source draws. -/
theorem direct_executes (rates : Array ℝ) (hr : ∀ a ∈ rates.toList, 0 ≤ a)
    (hA : 0 < rates.toList.sum) (now e u : ℝ) (he : 0 < e)
    (hu : 0 ≤ u ∧ u < 1) (j : Nat)
    (hj : selection rates.toList u = some j) :
    direct realArithmetic (tapeSource ℝ) rates now
      ⟨[u], [e]⟩ = .ok (some ⟨now + e / rates.toList.sum, j⟩, ⟨[], []⟩) := by
  have ht : now < now + e / rates.toList.sum := lt_add_of_pos_right _ (div_pos he hA)
  have hj' : weightedIndex realArithmetic rates (u * rates.toList.sum) = .ok j := by
    simp only [weightedIndex]
    change (match selection rates.toList u with | some i => Except.ok i | none => Except.error Error.selectionFailure) = Except.ok j
    rw [hj]
  unfold direct
  rw [checkRates_real rates hr]
  simp only [Bind.bind, Except.bind, sumRates_real]
  have hd : drawExponential realArithmetic (tapeSource ℝ) (⟨[u], [e]⟩ : Tape ℝ) =
      .ok (e, ⟨[u], []⟩) := by simp [drawExponential, tapeSource, realArithmetic, Bind.bind, Except.bind, not_le.mpr he] <;> rfl
  have hu' : drawUniform realArithmetic (tapeSource ℝ) (⟨[u], []⟩ : Tape ℝ) =
      .ok (u, ⟨[], []⟩) := by simp [drawUniform, tapeSource, realArithmetic, Bind.bind, Except.bind, not_lt.mpr hu.1, not_le.mpr hu.2] <;> rfl
  simp only [realArithmetic] at hd hu' hj' ⊢
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, hA, decide_true,
    hd, hu', Except.bind, hj', ht, Bool.true_and]
  rfl

/-- All clock/mark observables, from two independent uniforms through actual selection. -/
theorem direct_pair_probability (rates : List ℝ) (hr : ∀ a ∈ rates, 0 ≤ a)
    (hA : 0 < rates.sum) (i : Nat) (hi : i < rates.length)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (unitUniform.prod unitUniform)
      {p : ℝ × ℝ | exponentialClock rates.sum p.1 ∈ s ∧ selection rates p.2 = some i} =
      expMeasure rates.sum s * ENNReal.ofReal (rates[i] / rates.sum) := by
  change (unitUniform.prod unitUniform)
    ((exponentialClock rates.sum ⁻¹' s) ×ˢ (selection rates ⁻¹' {some i})) = _
  rw [Measure.prod_prod, selection_probability rates hr hA i hi,
    ← Measure.map_apply (measurable_exponentialClock _) hs,
    exponentialClock_map_uniform rates.sum hA]

/-- The ideal inverse-transform inputs refine the complete real Direct function. -/
theorem direct_uniform_executes (rates : Array ℝ) (hr : ∀ a ∈ rates.toList, 0 ≤ a)
    (hA : 0 < rates.toList.sum) (now v u : ℝ) (hv : v ∈ Ioo 0 1)
    (hu : u ∈ Ioo 0 1) (i : Nat) (hi : selection rates.toList u = some i) :
    direct realArithmetic (tapeSource ℝ) rates now ⟨[u], [-log v]⟩ =
      .ok (some ⟨now + exponentialClock rates.toList.sum v, i⟩, ⟨[], []⟩) := by
  have he : 0 < -log v := neg_pos.mpr (log_neg hv.1 hv.2)
  exact direct_executes rates hr hA now (-log v) u he ⟨hu.1.le, hu.2⟩ i hi

lemma unitUniform_ae_mem : ∀ᵐ u : ℝ ∂unitUniform, u ∈ Ioo 0 1 := by
  exact ae_restrict_mem measurableSet_Ioo

lemma unitUniform_pair_ae_mem : ∀ᵐ p : ℝ × ℝ ∂unitUniform.prod unitUniform,
    p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo 0 1 := by
  rw [Measure.ae_prod_iff_ae_ae (by measurability)]
  filter_upwards [unitUniform_ae_mem] with v hv
  filter_upwards [unitUniform_ae_mem] with u hu
  exact ⟨hv, hu⟩

/-- End-to-end joint law of the complete executable real Direct function. -/
theorem direct_executable_joint_tail (rates : Array ℝ)
    (hr : ∀ a ∈ rates.toList, 0 ≤ a) (hA : 0 < rates.toList.sum)
    (i : Nat) (hi : i < rates.size) (t : ℝ) (ht : 0 ≤ t) :
    (unitUniform.prod unitUniform) {p : ℝ × ℝ | ∃ (e : Event ℝ) (r : Tape ℝ),
      direct realArithmetic (tapeSource ℝ) rates 0 ⟨[p.2], [-log p.1]⟩ = .ok (some e, r) ∧
        t < e.time ∧ e.reaction = i} =
    ENNReal.ofReal ((rates[i] / rates.toList.sum) * clockSurvival rates.toList.sum t) := by
  have hae : {p : ℝ × ℝ | ∃ (e : Event ℝ) (r : Tape ℝ),
      direct realArithmetic (tapeSource ℝ) rates 0 ⟨[p.2], [-log p.1]⟩ = .ok (some e, r) ∧
        t < e.time ∧ e.reaction = i} =ᵐ[unitUniform.prod unitUniform]
      {p : ℝ × ℝ | t < exponentialClock rates.toList.sum p.1 ∧ selection rates.toList p.2 = some i} := by
    filter_upwards [unitUniform_pair_ae_mem] with p hp
    obtain ⟨j, hj⟩ := chooseAux_exists rates.toList hr (p.2 * rates.toList.sum) 0
      (by nlinarith [hp.2.1]) (by simp only [zero_add]; nlinarith [hp.2.2]) 0
    have hj' : selection rates.toList p.2 = some j := hj
    have hex := direct_uniform_executes rates hr hA 0 p.1 p.2 hp.1 hp.2 j hj'
    simp only [zero_add] at hex
    apply propext
    constructor
    · rintro ⟨e, r, he, htime, hreaction⟩
      rw [hex] at he
      have hev := Option.some.inj (congrArg Prod.fst (Except.ok.inj he))
      have ht' : t < exponentialClock rates.toList.sum p.1 := by simpa [← hev] using htime
      have hjx : j = i := by simpa [← hev] using hreaction
      exact ⟨ht', by simpa [hjx] using hj'⟩
    · rintro ⟨htime, hselection⟩
      have hjx : j = i := Option.some.inj (hj'.symm.trans hselection)
      exact ⟨⟨exponentialClock rates.toList.sum p.1, j⟩, ⟨[], []⟩, hex, htime, hjx⟩
  rw [measure_congr hae]
  have hi' : i < rates.toList.length := by simpa using hi
  change (unitUniform.prod unitUniform) {p : ℝ × ℝ | exponentialClock rates.toList.sum p.1 ∈ Ioi t ∧ selection rates.toList p.2 = some i} = _
  rw [direct_pair_probability rates.toList hr hA i hi' (Ioi t) measurableSet_Ioi,
    exponential_measure_tail _ t hA ht, ← ENNReal.ofReal_mul (show 0 ≤ clockSurvival rates.toList.sum t from (exp_pos _).le)]
  congr 1
  rw [Array.getElem_toList]
  ring

end JumpProcessesLean.Proofs
