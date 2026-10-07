import JumpProcessesLean.FloatLibBackend
import JumpProcessesLean.Proofs.Specification
import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals.Certified
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof

namespace JumpProcessesLean.Proofs
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

noncomputable def floatReal (x : Binary64) : ℝ := Model.toReal (ExecFloat.Binary.toModel x)
noncomputable abbrev floatEpsilon (x : ℝ) : ℝ := Model.epsilonAt FloatFormat.binary64 x

theorem float_lt_real (a b : Binary64)
    (ha : ExecFloat.Binary.isFinite a = true) (hb : ExecFloat.Binary.isFinite b = true) :
    a < b ↔ floatReal a < floatReal b := by
  rw [ExecFloat.Binary.lt_iff_compare_eq_lt]
  exact Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite _ _ ha hb

theorem float_le_real (a b : Binary64)
    (ha : ExecFloat.Binary.isFinite a = true) (hb : ExecFloat.Binary.isFinite b = true) :
    a ≤ b ↔ floatReal a ≤ floatReal b := by
  rw [ExecFloat.Binary.le_iff_compare_eq_lt_or_eq,
    Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite _ _ ha hb,
    Model.compare_eq_some_eq_iff_toReal_eq_of_isFinite _ _ ha hb]
  constructor
  · rintro (h | h)
    · exact h.le
    · exact h.le
  · exact lt_or_eq_of_le

lemma float_decode_add (a b : Binary64) : ExecFloat.Binary.toModel (a + b) =
    Model.add (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b) := by
  rw [ExecFloat.Proof.add_notation_eq_spec, Model.Proof.add_eq_spec]
  change ExecFloat.Binary.toModel (ExecFloat.Binary.ofModel
    (Model.Spec.add (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b))) = _
  simp

lemma float_decode_div (a b : Binary64) : ExecFloat.Binary.toModel (a / b) =
    Model.div (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b) := by
  rw [ExecFloat.Proof.div_notation_eq_spec, Model.Proof.div_eq_spec]
  change ExecFloat.Binary.toModel (ExecFloat.Binary.ofModel
    (Model.Spec.div (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b))) = _
  simp

/-- Concrete half-ULP bounds include gradual underflow and require finite outputs. -/
theorem float_add_error (a b : Binary64)
    (ha : ExecFloat.Binary.isFinite a = true) (hb : ExecFloat.Binary.isFinite b = true)
    (hc : ExecFloat.Binary.isFinite (a + b) = true) :
    |floatReal (a + b) - (floatReal a + floatReal b)| ≤ floatEpsilon (floatReal a + floatReal b) := by
  unfold floatReal
  rw [float_decode_add]
  exact Model.abs_toReal_add_sub_le _ _ rfl ha hb (by simpa only [ExecFloat.Binary.isFinite, float_decode_add] using hc)

theorem float_div_error (a b : Binary64)
    (ha : ExecFloat.Binary.isFinite a = true) (hb : ExecFloat.Binary.isFinite b = true)
    (hb0 : Model.isZero (ExecFloat.Binary.toModel b) = false)
    (hc : ExecFloat.Binary.isFinite (a / b) = true) :
    |floatReal (a / b) - floatReal a / floatReal b| ≤ floatEpsilon (floatReal a / floatReal b) := by
  unfold floatReal
  rw [float_decode_div]
  exact Model.abs_toReal_div_sub_le _ _ rfl ha hb hb0
    (by simpa only [ExecFloat.Binary.isFinite, float_decode_div] using hc)

lemma float_decode_sub (a b : Binary64) : ExecFloat.Binary.toModel (a - b) =
    Model.sub (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b) := by
  rw [ExecFloat.Proof.sub_notation_eq_spec, Model.Proof.sub_eq_spec]
  change ExecFloat.Binary.toModel (ExecFloat.Binary.ofModel
    (Model.Spec.sub (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b))) = _
  simp

lemma float_decode_mul (a b : Binary64) : ExecFloat.Binary.toModel (a * b) =
    Model.mul (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b) := by
  rw [ExecFloat.Proof.mul_notation_eq_spec, Model.Proof.mul_eq_spec]
  change ExecFloat.Binary.toModel (ExecFloat.Binary.ofModel
    (Model.Spec.mul (ExecFloat.Binary.toModel a) (ExecFloat.Binary.toModel b))) = _
  simp

theorem float_sub_error (a b : Binary64)
    (ha : ExecFloat.Binary.isFinite a = true) (hb : ExecFloat.Binary.isFinite b = true)
    (hc : ExecFloat.Binary.isFinite (a - b) = true) :
    |floatReal (a - b) - (floatReal a - floatReal b)| ≤ floatEpsilon (floatReal a - floatReal b) := by
  unfold floatReal
  rw [float_decode_sub]
  exact Model.abs_toReal_sub_sub_le _ _ rfl ha hb
    (by simpa only [ExecFloat.Binary.isFinite, float_decode_sub] using hc)

theorem float_mul_error (a b : Binary64)
    (ha : ExecFloat.Binary.isFinite a = true) (hb : ExecFloat.Binary.isFinite b = true)
    (hc : ExecFloat.Binary.isFinite (a * b) = true) :
    |floatReal (a * b) - floatReal a * floatReal b| ≤ floatEpsilon (floatReal a * floatReal b) := by
  unfold floatReal
  rw [float_decode_mul]
  exact Model.abs_toReal_mul_sub_le _ _ rfl ha hb
    (by simpa only [ExecFloat.Binary.isFinite, float_decode_mul] using hc)

/-- Exact bound for the time expression used by Direct, NRM initialization, and accepted RSSA. -/
theorem float_clock_time_error (now elapsed total : Binary64)
    (hn : ExecFloat.Binary.isFinite now = true) (he : ExecFloat.Binary.isFinite elapsed = true)
    (hT : ExecFloat.Binary.isFinite total = true)
    (hT0 : Model.isZero (ExecFloat.Binary.toModel total) = false)
    (hq : ExecFloat.Binary.isFinite (elapsed / total) = true)
    (ht : ExecFloat.Binary.isFinite (now + elapsed / total) = true) :
    |floatReal (now + elapsed / total) - (floatReal now + floatReal elapsed / floatReal total)| ≤
      floatEpsilon (floatReal now + floatReal (elapsed / total)) +
      floatEpsilon (floatReal elapsed / floatReal total) := by
  have ha := float_add_error now (elapsed / total) hn hq ht
  have hd := float_div_error elapsed total he hT hT0 hq
  calc
    _ = |(floatReal (now + elapsed / total) - (floatReal now + floatReal (elapsed / total))) +
          (floatReal (elapsed / total) - floatReal elapsed / floatReal total)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add ha hd)

/-- FloatLib certifies the logarithm's numerical error when its checked kernel succeeds. -/
theorem float_certified_log_error (u l : Binary64)
    (hl : ExecFloat.Binary.Certified.log u = some l) :
    |floatReal l - log (floatReal u)| ≤ floatEpsilon (log (floatReal u)) := by
  unfold floatReal
  rw [ExecFloat.Binary.Certified.toReal_of_log_eq_some hl]
  exact Model.abs_roundAt_sub_le _ _

/-- The ordinary log has a rigorous a-posteriori bound from a successful certificate. -/
theorem float_default_log_error (u l : Binary64)
    (hl : ExecFloat.Binary.Certified.log u = some l) :
    |floatReal (binary64Log u) - log (floatReal u)| ≤
      |floatReal (binary64Log u) - floatReal l| + floatEpsilon (log (floatReal u)) := by
  exact (abs_sub_le (floatReal (binary64Log u)) (floatReal l) (log (floatReal u))).trans
    (add_le_add (le_refl _) (float_certified_log_error u l hl))

/-- Stable selection interval under errors in the threshold and both CDF endpoints. -/
theorem selection_margin_stable (x lo hi xf lof hif η : ℝ) (hη : 0 ≤ η)
    (hx : |xf - x| ≤ η) (hl : |lof - lo| ≤ η) (hh : |hif - hi| ≤ η)
    (hlo : lo + 2 * η < x) (hhi : x < hi - 2 * η) : lof < xf ∧ xf < hif := by
  have hx' := abs_le.mp hx
  have hl' := abs_le.mp hl
  have hh' := abs_le.mp hh
  constructor <;> linarith

/-- NRM chooses the same winner whenever rounding is smaller than half the clock gap. -/
theorem race_margin_stable {n : Nat} (c cf : Fin n → ℝ) (η : ℝ) (i : Fin n)
    (he : ∀ j, |cf j - c j| ≤ η)
    (hgap : ∀ j, j ≠ i → c i + 2 * η < c j) :
    ∀ j, j ≠ i → cf i < cf j := by
  intro j hj
  have hi := abs_le.mp (he i)
  have hj' := abs_le.mp (he j)
  linarith [hgap j hj]

/-- The RSSA comparison is stable away from the acceptance threshold. -/
theorem rejection_margin_stable (v a vf af η : ℝ)
    (hv : |vf - v| ≤ η) (ha : |af - a| ≤ η) (hgap : 2 * η < |v - a|) :
    (vf ≤ af ↔ v ≤ a) := by
  have hv' := abs_le.mp hv
  have ha' := abs_le.mp ha
  rcases le_total v a with h | h
  · have hg : v + 2 * η < a := by rw [abs_of_nonpos (sub_nonpos.mpr h)] at hgap; linarith
    have hf : vf ≤ af := by linarith
    simp [h, hf]
  · have hg : a + 2 * η < v := by rw [abs_of_nonneg (sub_nonneg.mpr h)] at hgap; linarith
    have hf : ¬vf ≤ af := by linarith
    have hreal : ¬v ≤ a := by linarith
    simp [hreal, hf]

/-- Distribution approximation under a common-input coupling.
The bad set accounts for source approximation, branch margins, overflow, and fuel failure.
The result compares joint tails without claiming total-variation convergence to a continuous law. -/
theorem coupled_joint_tail_bounds {Ω ι : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (T Tf : Ω → ℝ) (I If : Ω → ι) (bad : Set Ω)
    (hbad : MeasurableSet bad) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ ω ∉ bad, |Tf ω - T ω| ≤ δ ∧ If ω = I ω)
    (i : ι) (t : ℝ) :
    μ {ω | t + δ < T ω ∧ I ω = i} ≤ μ {ω | t < Tf ω ∧ If ω = i} + μ bad ∧
      μ {ω | t < Tf ω ∧ If ω = i} ≤ μ {ω | t - δ < T ω ∧ I ω = i} + μ bad := by
  constructor
  · apply le_trans (measure_mono (t := {ω | t < Tf ω ∧ If ω = i} ∪ bad) ?_)
      (measure_union_le _ _)
    intro ω hω
    by_cases hb : ω ∈ bad
    · exact Or.inr hb
    · obtain ⟨he, hm⟩ := hgood ω hb
      have habs := abs_le.mp he
      exact Or.inl ⟨by linarith [hω.1], hm.trans hω.2⟩
  · apply le_trans (measure_mono (t := {ω | t - δ < T ω ∧ I ω = i} ∪ bad) ?_)
      (measure_union_le _ _)
    intro ω hω
    by_cases hb : ω ∈ bad
    · exact Or.inr hb
    · obtain ⟨he, hm⟩ := hgood ω hb
      have habs := abs_le.mp he
      exact Or.inl ⟨by linarith [hω.1], hm.symm.trans hω.2⟩

/-- Accumulated rounding budget of the actual left fold used for rates and RSSA clocks. -/
noncomputable def foldRoundBudget (acc : Binary64) : List Binary64 → ℝ
  | [] => 0
  | x :: xs => floatEpsilon (floatReal acc + floatReal x) + foldRoundBudget (acc + x) xs

def FoldFinite (acc : Binary64) : List Binary64 → Prop
  | [] => ExecFloat.Binary.isFinite acc = true
  | x :: xs => ExecFloat.Binary.isFinite acc = true ∧ ExecFloat.Binary.isFinite x = true ∧ FoldFinite (acc + x) xs

lemma foldFinite_head (acc : Binary64) (xs : List Binary64) (h : FoldFinite acc xs) :
    ExecFloat.Binary.isFinite acc = true := by
  cases xs with
  | nil => exact h
  | cons x xs => exact h.1

/-- No relative-error assumption is needed near subnormal values. -/
theorem float_fold_sum_error (acc : Binary64) (xs : List Binary64) (h : FoldFinite acc xs) :
    |floatReal (xs.foldl (· + ·) acc) - (floatReal acc + (xs.map floatReal).sum)| ≤ foldRoundBudget acc xs := by
  induction xs generalizing acc with
  | nil => simp [foldRoundBudget]
  | cons x xs ih =>
    have hf := foldFinite_head (acc + x) xs h.2.2
    have ha := float_add_error acc x h.1 h.2.1 hf
    have hb := ih (acc + x) h.2.2
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldRoundBudget]
    calc
      _ = |(floatReal (xs.foldl (· + ·) (acc + x)) -
          (floatReal (acc + x) + (xs.map floatReal).sum)) +
          (floatReal (acc + x) - (floatReal acc + floatReal x))| := by congr 1; ring
      _ ≤ foldRoundBudget (acc + x) xs + floatEpsilon (floatReal acc + floatReal x) :=
        (abs_add_le _ _).trans (add_le_add hb ha)
      _ = _ := add_comm _ _

lemma abs_four_sum_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))) (le_refl _))

/-- Explicit error propagation for the actual Gibson–Bruck float rescaling expression. -/
theorem float_nrm_rescale_error (now oldRate newRate oldTime : Binary64)
    (hn : ExecFloat.Binary.isFinite now = true) (ho : ExecFloat.Binary.isFinite oldRate = true)
    (hnew : ExecFloat.Binary.isFinite newRate = true) (ht : ExecFloat.Binary.isFinite oldTime = true)
    (hz : Model.isZero (ExecFloat.Binary.toModel newRate) = false)
    (hq : ExecFloat.Binary.isFinite (oldRate / newRate) = true)
    (hd : ExecFloat.Binary.isFinite (oldTime - now) = true)
    (hp : ExecFloat.Binary.isFinite ((oldRate / newRate) * (oldTime - now)) = true)
    (hs : ExecFloat.Binary.isFinite (rescaleClock binary64Arithmetic now oldRate newRate oldTime) = true) :
    |floatReal (rescaleClock binary64Arithmetic now oldRate newRate oldTime) -
      (floatReal now + (floatReal oldRate / floatReal newRate) * (floatReal oldTime - floatReal now))| ≤
      floatEpsilon (floatReal now + floatReal ((oldRate / newRate) * (oldTime - now))) +
      floatEpsilon (floatReal (oldRate / newRate) * floatReal (oldTime - now)) +
      |floatReal (oldRate / newRate)| * floatEpsilon (floatReal oldTime - floatReal now) +
      |floatReal oldTime - floatReal now| * floatEpsilon (floatReal oldRate / floatReal newRate) := by
  change ExecFloat.Binary.isFinite (now + (oldRate / newRate) * (oldTime - now)) = true at hs
  have h1 := float_add_error now ((oldRate / newRate) * (oldTime - now)) hn hp hs
  have h2 := float_mul_error (oldRate / newRate) (oldTime - now) hq hd hp
  have h3 := float_sub_error oldTime now ht hn hd
  have h4 := float_div_error oldRate newRate ho hnew hz hq
  change |floatReal (now + (oldRate / newRate) * (oldTime - now)) - _| ≤ _
  have heq : floatReal (now + (oldRate / newRate) * (oldTime - now)) -
      (floatReal now + (floatReal oldRate / floatReal newRate) * (floatReal oldTime - floatReal now)) =
      (floatReal (now + (oldRate / newRate) * (oldTime - now)) -
        (floatReal now + floatReal ((oldRate / newRate) * (oldTime - now)))) +
      (floatReal ((oldRate / newRate) * (oldTime - now)) -
        floatReal (oldRate / newRate) * floatReal (oldTime - now)) +
      floatReal (oldRate / newRate) * (floatReal (oldTime - now) - (floatReal oldTime - floatReal now)) +
      (floatReal (oldRate / newRate) - floatReal oldRate / floatReal newRate) * (floatReal oldTime - floatReal now) := by ring
  rw [heq]
  refine (abs_four_sum_le _ _ _ _).trans ?_
  simp only [abs_mul]
  exact add_le_add (add_le_add (add_le_add h1 h2)
    (mul_le_mul_of_nonneg_left h3 (abs_nonneg _)))
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left h4 (abs_nonneg _))

end JumpProcessesLean.Proofs
