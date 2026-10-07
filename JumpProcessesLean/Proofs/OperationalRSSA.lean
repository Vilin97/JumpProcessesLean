import JumpProcessesLean.Proofs.OperationalDirect
import JumpProcessesLean.Proofs.ExponentialSum
import JumpProcessesLean.RSSA

namespace JumpProcessesLean.Proofs
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma unitUniform_le_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    unitUniform (Iic p) = ENNReal.ofReal p := by
  rw [unitUniform, Measure.restrict_apply measurableSet_Iic]
  have hae : Iic p ∩ Ioo 0 1 =ᵐ[volume] Ioc 0 p := by
    have hz : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := by rw [ae_iff]; simp
    filter_upwards [hz] with u hu
    apply propext
    simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
    constructor
    · intro h; exact ⟨h.2.1, h.1⟩
    · intro h
      exact ⟨h.2, h.1, lt_of_le_of_ne (h.2.trans hp1) hu⟩
  rw [measure_congr hae, Real.volume_Ioc, sub_zero]

/-- The lower shortcut and actual rejection comparison have the correct acceptance mass. -/
theorem rssa_accept_probability (lower actual upper : ℝ)
    (hl : 0 ≤ lower) (hla : lower ≤ actual) (hau : actual ≤ upper) :
    unitUniform {v | rssaAccept realArithmetic lower actual (v * upper) = true} =
      ENNReal.ofReal (if upper = 0 then 0 else actual / upper) := by
  have ha : 0 ≤ actual := hl.trans hla
  have hu : 0 ≤ upper := ha.trans hau
  have hc (v : ℝ) := rssa_lower_shortcut lower actual (v * upper) hla
  simp_rw [hc]
  by_cases hp : 0 < actual
  · have hup : 0 < upper := hp.trans_le hau
    have hs : {v : ℝ | decide (0 < actual ∧ v * upper ≤ actual) = true} =
        Iic (actual / upper) := by
      ext v; simp [realArithmetic, hp, mem_Iic, le_div_iff₀ hup]
    rw [hs, unitUniform_le_probability _ (div_nonneg ha hu) ((div_le_one hup).mpr hau)]
    simp [hup.ne']
  · have hz : actual = 0 := le_antisymm (le_of_not_gt hp) ha
    simp [realArithmetic, hp, hz]

/-- One concrete RSSA proposal accepts reaction i with probability a_i / B. -/
theorem rssa_proposal_probability (rates lower upper : List ℝ)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (hB : 0 < upper.sum) (i : Nat) (hi : i < rates.length) :
    (unitUniform.prod unitUniform)
      {p : ℝ × ℝ | selection upper p.1 = some i ∧
        rssaAccept realArithmetic (lower[i]'(by omega)) rates[i] (p.2 * upper[i]'(by omega)) = true} =
      ENNReal.ofReal (rates[i] / upper.sum) := by
  have hu : ∀ a ∈ upper, 0 ≤ a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hjr : j < rates.length := by omega
    exact ((hb j hjr).1.trans (hb j hjr).2.1).trans (hb j hjr).2.2
  change (unitUniform.prod unitUniform)
    ((selection upper ⁻¹' {some i}) ×ˢ {v | rssaAccept realArithmetic (lower[i]'(by omega))
      rates[i] (v * upper[i]'(by omega)) = true}) = _
  rw [Measure.prod_prod, selection_probability upper hu hB i (by omega),
    rssa_accept_probability _ _ _ (hb i hi).1 (hb i hi).2.1 (hb i hi).2.2]
  by_cases hz : upper[i]'(by omega) = 0
  · have ha0 : rates[i] = 0 := le_antisymm (by simpa [hz] using (hb i hi).2.2)
      ((hb i hi).1.trans (hb i hi).2.1)
    simp [hz, ha0]
  · rw [ite_eq_right hz, ← ENNReal.ofReal_mul (div_nonneg (hu _ (List.getElem_mem (by omega))) hB.le)]
    congr 1
    field_simp

/-- Recursive subprobability law of acceptance before the cap, for one specified mark.
Each recursive stage adds a genuine independent exponential clock. -/
noncomputable def rejectionClockLaw (B q p : ℝ) : Nat → Measure ℝ
  | 0 => 0
  | fuel + 1 => ENNReal.ofReal p • expMeasure B +
      ENNReal.ofReal q • (expMeasure B).conv (rejectionClockLaw B q p fuel)

/-- The law of the finite rejection loop is the sum of its actual success branches. -/
theorem rejectionClockLaw_expansion (B q p : ℝ) (hB : 0 < B) (hq : 0 ≤ q) (hp : 0 ≤ p) (fuel : Nat) :
    rejectionClockLaw B q p fuel =
      ∑ k ∈ Finset.range fuel, ENNReal.ofReal (q ^ k * p) • sumExponentialLaw B (k + 1) := by
  let : IsProbabilityMeasure (expMeasure B) := isProbabilityMeasure_expMeasure hB
  have hprob (k : Nat) : IsProbabilityMeasure (sumExponentialLaw B k) := by
    induction k with
    | zero => simp only [sumExponentialLaw]; infer_instance
    | succ k ih =>
      let : IsProbabilityMeasure (sumExponentialLaw B k) := ih
      simp only [sumExponentialLaw]; infer_instance
  let (k : Nat) : IsProbabilityMeasure (sumExponentialLaw B k) := hprob k
  have hsf (s : Finset Nat) : SFinite (∑ k ∈ s, ENNReal.ofReal (q ^ k * p) • sumExponentialLaw B (k + 1)) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; infer_instance
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      let : SFinite (∑ k ∈ s, ENNReal.ofReal (q ^ k * p) • sumExponentialLaw B (k + 1)) := ih
      infer_instance
  let (s : Finset Nat) : SFinite (∑ k ∈ s, ENNReal.ofReal (q ^ k * p) • sumExponentialLaw B (k + 1)) := hsf s
  have hstep (k : Nat) : (expMeasure B).conv (sumExponentialLaw B (k + 1)) = sumExponentialLaw B (k + 2) := rfl
  have hconv (s : Finset Nat) : (expMeasure B).conv (∑ k ∈ s, ENNReal.ofReal (q ^ k * p) • sumExponentialLaw B (k + 1)) =
      ∑ k ∈ s, (expMeasure B).conv (ENNReal.ofReal (q ^ k * p) • sumExponentialLaw B (k + 1)) := by
    induction s using Finset.induction_on with
    | empty => simp [Measure.conv_zero]
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, Measure.conv_add, ih]
  induction fuel with
  | zero => simp [rejectionClockLaw]
  | succ fuel ih =>
    rw [rejectionClockLaw, ih]
    rw [hconv]
    simp_rw [Measure.conv_smul_right, Finset.smul_sum, smul_smul,
      ← ENNReal.ofReal_mul hq, hstep]
    rw [Finset.sum_range_succ']
    have hone : sumExponentialLaw B 1 = expMeasure B := by
      simp only [sumExponentialLaw, Measure.conv_dirac, add_zero]
      exact Measure.map_id
    simp only [pow_zero, one_mul, hone]
    rw [add_comm (ENNReal.ofReal p • expMeasure B)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ]
    ring_nf

/-- Unbounded independent rejection, decomposed by the first successful proposal. -/
noncomputable def infiniteRejectionClockLaw (B q p : ℝ) : Measure ℝ :=
  Measure.sum (fun k : Nat => ENNReal.ofReal (q ^ k * p) • sumExponentialLaw B (k + 1))

/-- The sum law is derived from independent exponential additions and geometric branches. -/
theorem infinite_rejection_clock_law (B q p : ℝ)
    (hB : 0 < B) (hq0 : 0 ≤ q) (hq1 : q < 1) (hp : 0 ≤ p) :
    infiniteRejectionClockLaw B q p =
      ENNReal.ofReal (p / (1 - q)) • expMeasure (B * (1 - q)) := by
  have hq : 0 < 1 - q := by linarith
  unfold infiniteRejectionClockLaw
  simp_rw [sum_exponentials_erlang B hB]
  have hcoeff (k : Nat) : 0 ≤ q ^ k * p := mul_nonneg (pow_nonneg hq0 _) hp
  have hmeas (k : Nat) : Measurable (fun t : ℝ =>
      ENNReal.ofReal (q ^ k * p) * erlangPDF B k t) :=
    measurable_const.mul (measurable_erlangPDF B k)
  have hterm (k : Nat) : ENNReal.ofReal (q ^ k * p) • erlangMeasure B k =
      volume.withDensity (fun t => ENNReal.ofReal (q ^ k * p) * erlangPDF B k t) := by
    exact (withDensity_smul _ (measurable_erlangPDF B k)).symm
  simp_rw [hterm]
  rw [← withDensity_tsum hmeas]
  change _ = ENNReal.ofReal (p / (1 - q)) • volume.withDensity (exponentialPDF (B * (1 - q)))
  rw [← withDensity_smul _ (by exact (measurable_exponentialPDFReal _).ennreal_ofReal)]
  congr 1
  funext t
  simp only [ENNReal.tsum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases ht : 0 ≤ t
  · have hd (k : Nat) : q ^ k * p * erlangDensity B k t =
        (p * B * exp (-(B * t))) * ((q * B * t) ^ k / (k.factorial : ℝ)) := by
      unfold erlangDensity
      rw [ite_eq_left ht, mul_pow, mul_pow, pow_succ]
      ring
    have hn (k : Nat) : 0 ≤ q ^ k * p * erlangDensity B k t := by
      unfold erlangDensity
      rw [ite_eq_left ht]
      positivity
    have hexp := NormedSpace.expSeries_div_hasSum_exp (q * B * t)
    have hsumm : Summable (fun k : Nat => q ^ k * p * erlangDensity B k t) := by
      simp_rw [hd]
      exact hexp.summable.mul_left _
    simp only [erlangPDF]
    simp_rw [← ENNReal.ofReal_mul (hcoeff _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg hn hsumm]
    simp_rw [hd]
    rw [tsum_mul_left]
    rw [show (∑' k : Nat, (q * B * t) ^ k / (k.factorial : ℝ)) = exp (q * B * t) by
      simpa only [← Real.exp_eq_exp_ℝ] using hexp.tsum_eq]
    rw [exponentialPDF_of_nonneg ht,
      ← ENNReal.ofReal_mul (div_nonneg hp hq.le)]
    congr 1
    rw [mul_assoc, ← exp_add]
    have he : -(B * t) + q * B * t = -(B * (1 - q) * t) := by ring
    rw [he]
    field_simp
  · simp [erlangPDF, erlangDensity, ht, exponentialPDF_of_neg (lt_of_not_ge ht)]

/-- RSSA's resulting mark-and-clock law equals the Direct/NRM law. -/
theorem rssa_rejection_clock_law {n : Nat} (rates upper : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ rates i) (hu : ∀ i, rates i ≤ upper i)
    (hA : 0 < ∑ i, rates i) (i : Fin n) :
    infiniteRejectionClockLaw (∑ j, upper j)
      (1 - (∑ j, rates j) / (∑ j, upper j)) (rates i / (∑ j, upper j)) =
      ENNReal.ofReal (rates i / (∑ j, rates j)) • expMeasure (∑ j, rates j) := by
  have hB : 0 < ∑ j, upper j := hA.trans_le (Finset.sum_le_sum (fun j _ => hu j))
  obtain ⟨hq0, hq1⟩ := rejection_probability_bounds rates upper hr hu hA
  rw [infinite_rejection_clock_law _ _ _ hB hq0 hq1 (div_nonneg (hr i) hB.le)]
  congr 2 <;> field_simp [hA.ne', hB.ne'] <;> ring

end JumpProcessesLean.Proofs
