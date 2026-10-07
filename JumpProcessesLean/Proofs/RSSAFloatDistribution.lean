import JumpProcessesLean.Proofs.RSSAFloatLaw
import JumpProcessesLean.Proofs.RealSamplerLaws

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

abbrev RSSABranchInput (k : Nat) := (Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ × ℝ)
abbrev RSSAStoppingInput (n : Nat) := Σ b : Nat × Fin n, RSSABranchInput b.1

lemma measurable_branch_injection {n : Nat} (b : Nat × Fin n) :
    Measurable (fun p : RSSABranchInput b.1 => (⟨b, p⟩ : RSSAStoppingInput n)) := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mp hs b

lemma measurable_stopping_function {n : Nat} {X : Type} [MeasurableSpace X]
    (f : RSSAStoppingInput n → X)
    (hf : ∀ b, Measurable (fun p => f ⟨b, p⟩)) : Measurable f := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr (fun b => hf b hs)

noncomputable def rssaBranchInputs (rates lower upper : List ℝ) (k i : Nat) :
    Measure (RSSABranchInput k) :=
  (((Measure.pi (fun _ : Fin (k + 1) => unitUniform)).prod
    (Measure.pi (fun _ : Fin (k + 1) => unitUniform.prod unitUniform))).restrict
      (univ ×ˢ proposalBranch rates lower upper k i))

/-- The IID first-success stopping measure. Each summand is an unnormalized
primitive product measure restricted to its actual first-success branch. -/
noncomputable def rssaStoppingInputs {n : Nat} (rates lower upper : List ℝ) :
    Measure (RSSAStoppingInput n) :=
  Measure.sum (fun b : Nat × Fin n =>
    (rssaBranchInputs rates lower upper b.1 b.2.val).map (Sigma.mk b))

noncomputable def rssaStoppingTime {n : Nat} (upper : List ℝ) (p : RSSAStoppingInput n) : ℝ :=
  ∑ j, exponentialClock upper.sum (p.2.1 j)

def rssaStoppingMark {n : Nat} (p : RSSAStoppingInput n) : Fin n := p.1.2

lemma measurable_rssaStoppingTime {n : Nat} (upper : List ℝ) :
    Measurable (@rssaStoppingTime n upper) := by
  apply measurable_stopping_function
  intro b
  change Measurable (fun p : RSSABranchInput b.1 => ∑ j, exponentialClock upper.sum (p.1 j))
  unfold exponentialClock
  fun_prop

lemma measurable_rssaStoppingMark (n : Nat) : Measurable (@rssaStoppingMark n) := by
  apply measurable_stopping_function
  intro b
  change Measurable (fun _ : RSSABranchInput b.1 => b.2)
  exact measurable_const

/-- The joint time/mark law is derived directly from the primitive stopping input.
Neither the stopping input nor its successful branches are normalized by hand. -/
theorem rssa_stopping_input_marked_law {n : Nat} (rates lower upper : List ℝ)
    (hn : rates.length = n)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (hA : 0 < rates.sum) (hB : 0 < upper.sum) (hAB : rates.sum ≤ upper.sum)
    (i : Fin n) (s : Set ℝ) (hs : MeasurableSet s) :
    (rssaStoppingInputs (n := n) rates lower upper)
      {p | rssaStoppingTime upper p ∈ s ∧ rssaStoppingMark p = i} =
      ENNReal.ofReal (rates[i.val]'(by omega) / rates.sum) * expMeasure rates.sum s := by
  have hm : MeasurableSet {p : RSSAStoppingInput n |
      rssaStoppingTime upper p ∈ s ∧ rssaStoppingMark p = i} :=
    ((measurable_rssaStoppingTime upper) hs).inter
      ((measurable_rssaStoppingMark n) (measurableSet_singleton i))
  unfold rssaStoppingInputs
  rw [Measure.sum_apply _ hm, ENNReal.tsum_prod']
  have hterm (k : Nat) (j : Fin n) :
      ((rssaBranchInputs rates lower upper k j.val).map (Sigma.mk (k, j)))
        {p | rssaStoppingTime upper p ∈ s ∧ rssaStoppingMark p = i} =
      if j = i then rssaExecutableBranchLaw rates lower upper k i.val s else 0 := by
    rw [Measure.map_apply (measurable_branch_injection (k, j)) hm]
    by_cases hj : j = i
    · subst j
      simp only [rssaStoppingTime, rssaStoppingMark, true_and, and_true, ite_true]
      change _ = (rssaBranchInputs rates lower upper k i.val).map
        (fun p => ∑ j, exponentialClock upper.sum (p.1 j)) s
      rw [Measure.map_apply (by unfold exponentialClock; fun_prop) hs]
      congr 1
      ext p
      simp
    · simp [rssaStoppingMark, hj]
  simp_rw [hterm]
  simp only [tsum_fintype, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Measure.sum_apply _ hs]
  change rssaExecutableLaw rates lower upper i.val s = _
  rw [rssa_executable_clock_law rates lower upper hshape hb hA hB hAB i.val (by omega),
    Measure.smul_apply, smul_eq_mul]

noncomputable def rssaStoppingFloatSample {n : Nat} (rates : Array Binary64)
    (bounds : RateBounds Binary64) (now : Binary64) (cap : Nat)
    (ef uf vf : (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (suffixU suffixE : RSSAStoppingInput n → List Binary64) (p : RSSAStoppingInput n) :
    Option (Event Binary64) :=
  match rssa binary64Arithmetic (tapeSource Binary64) rates bounds now
      ⟨proposalFloatUniforms (uf p) (vf p) ++ suffixU p, List.ofFn (ef p) ++ suffixE p⟩ cap with
  | .ok (e, _) => e
  | _ => none

noncomputable def rssaStoppingFloatTime {n : Nat} (rates : Array Binary64)
    (bounds : RateBounds Binary64) (now : Binary64) (cap : Nat)
    (ef uf vf : (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (suffixU suffixE : RSSAStoppingInput n → List Binary64) (p : RSSAStoppingInput n) : ℝ :=
  ((rssaStoppingFloatSample rates bounds now cap ef uf vf suffixU suffixE p).map
    (fun e => floatReal e.time)).getD 0 - floatReal now

noncomputable def rssaStoppingFloatMark {n : Nat} (rates : Array Binary64)
    (bounds : RateBounds Binary64) (now : Binary64) (cap : Nat)
    (ef uf vf : (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (suffixU suffixE : RSSAStoppingInput n → List Binary64) (p : RSSAStoppingInput n) : Option Nat :=
  (rssaStoppingFloatSample rates bounds now cap ef uf vf suffixU suffixE p).map Event.reaction

/-- Complete float RSSA joint-tail approximation. The bad set includes the
proposal cap, source error, overflow and failed input/branch certificates. -/
theorem rssa_float_joint_tail_approx {n : Nat} (rates : Array Binary64)
    (bounds : RateBounds Binary64) (hn : rates.size = n) (now : Binary64) (cap : Nat)
    (ef uf vf : (p : RSSAStoppingInput n) → Fin (p.1.1 + 1) → Binary64)
    (suffixU suffixE : RSSAStoppingInput n → List Binary64)
    (bad : Set (RSSAStoppingInput n)) (hbad : MeasurableSet bad)
    (δ η : ℝ) (hδ : 0 ≤ δ)
    (hshape : bounds.lower.size = rates.size ∧ bounds.upper.size = rates.size)
    (hb : ∀ (i : Nat) (hi : i < rates.size),
      0 ≤ floatReal (bounds.lower[i]'(by omega)) ∧
      floatReal (bounds.lower[i]'(by omega)) ≤ floatReal rates[i] ∧
      floatReal rates[i] ≤ floatReal (bounds.upper[i]'(by omega)))
    (hA : 0 < (rates.toList.map floatReal).sum)
    (hgood : ∀ p ∉ bad, p.1.1 < cap ∧
      (∀ q, (p.2.2 q).1 ∈ Ioo 0 1) ∧
      p.2.2 ∈ proposalBranch (rates.toList.map floatReal)
        (bounds.lower.toList.map floatReal) (bounds.upper.toList.map floatReal) p.1.1 p.1.2.val ∧
      RSSAFloatCertificate rates bounds now (ef p) (uf p) (vf p)
        (fun q => -log (p.2.1 q)) (fun q => (p.2.2 q).1) (fun q => (p.2.2 q).2) δ η)
    (i : Fin n) (t : ℝ) (ht : δ ≤ t) :
    let rr := rates.toList.map floatReal
    let lo := bounds.lower.toList.map floatReal
    let up := bounds.upper.toList.map floatReal
    let μ := rssaStoppingInputs (n := n) rr lo up
    ENNReal.ofReal ((rr[i.val]'(by change i.val < (rates.toList.map floatReal).length; simpa [hn] using i.isLt) / rr.sum) * clockSurvival rr.sum (t + δ)) ≤
      μ {p | t < rssaStoppingFloatTime rates bounds now cap ef uf vf suffixU suffixE p ∧
        rssaStoppingFloatMark rates bounds now cap ef uf vf suffixU suffixE p = some i.val} + μ bad ∧
    μ {p | t < rssaStoppingFloatTime rates bounds now cap ef uf vf suffixU suffixE p ∧
        rssaStoppingFloatMark rates bounds now cap ef uf vf suffixU suffixE p = some i.val} ≤
      ENNReal.ofReal ((rr[i.val]'(by change i.val < (rates.toList.map floatReal).length; simpa [hn] using i.isLt) / rr.sum) * clockSurvival rr.sum (t - δ)) + μ bad := by
  dsimp only
  let rr := rates.toList.map floatReal
  let lo := bounds.lower.toList.map floatReal
  let up := bounds.upper.toList.map floatReal
  have hl : lo.length = rr.length ∧ up.length = rr.length := by simpa [lo, up, rr] using hshape
  have hbl : ∀ (j : Nat) (hj : j < rr.length),
      0 ≤ lo[j]'(by omega) ∧ lo[j]'(by omega) ≤ rr[j] ∧ rr[j] ≤ up[j]'(by omega) := by
    intro j hj
    simpa [rr, lo, up] using hb j (by simpa [rr] using hj)
  have hup : ∀ a ∈ up, 0 ≤ a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hjr : j < rr.length := by omega
    exact ((hbl j hjr).1.trans (hbl j hjr).2.1).trans (hbl j hjr).2.2
  have hAB : rr.sum ≤ up.sum := by
    have he : List.ofFn (fun j : Fin rr.length => up[j.val]'(by omega)) = up := by
      apply List.ext_getElem (by simp [hl.2]); intro j hj hj'; simp
    calc
      rr.sum = ∑ j : Fin rr.length, rr[j.val] := by rw [← List.sum_ofFn, List.ofFn_getElem]
      _ ≤ ∑ j : Fin rr.length, up[j.val]'(by omega) :=
        Finset.sum_le_sum (fun j _ => (hbl j.val j.isLt).2.2)
      _ = up.sum := by rw [← List.sum_ofFn, he]
  have hB : 0 < up.sum := hA.trans_le hAB
  have hg : ∀ p ∉ bad,
      |rssaStoppingFloatTime rates bounds now cap ef uf vf suffixU suffixE p - rssaStoppingTime up p| ≤ δ ∧
      rssaStoppingFloatMark rates bounds now cap ef uf vf suffixU suffixE p = some (rssaStoppingMark p).val := by
    intro p hp
    obtain ⟨hcap, hu, hbranch, hc⟩ := hgood p hp
    have he := rssa_float_certificate_refines rates bounds now (ef p) (uf p) (vf p)
      _ _ _ δ η hc hup hB hu p.1.2.val
      (by intro q; exact (mem_pi.mp hbranch) q (mem_univ _)) (suffixU p) (suffixE p)
      (cap - (p.1.1 + 1))
    rw [show p.1.1 + 1 + (cap - (p.1.1 + 1)) = cap by omega] at he
    unfold rssaStoppingFloatTime rssaStoppingFloatMark rssaStoppingFloatSample
    rw [he.1]
    constructor
    · simpa only [Option.map_some, Option.getD_some, rssaStoppingTime, exponentialClock,
        Finset.sum_div, sub_sub, add_sub_cancel_left] using he.2
    · rfl
  have h := coupled_joint_tail_bounds (rssaStoppingInputs (n := n) rr lo up)
    (rssaStoppingTime up) (rssaStoppingFloatTime rates bounds now cap ef uf vf suffixU suffixE)
    (fun p => some (rssaStoppingMark p).val)
    (rssaStoppingFloatMark rates bounds now cap ef uf vf suffixU suffixE) bad hbad δ hδ hg (some i.val) t
  have htail (s : ℝ) (hs : 0 ≤ s) :
      (rssaStoppingInputs (n := n) rr lo up) {p | s < rssaStoppingTime up p ∧
        some (rssaStoppingMark p).val = some i.val} =
      ENNReal.ofReal ((rr[i.val]'(by simpa [rr, hn] using i.isLt) / rr.sum) * clockSurvival rr.sum s) := by
    have he : {p : RSSAStoppingInput n | s < rssaStoppingTime up p ∧
        some (rssaStoppingMark p).val = some i.val} =
        {p | rssaStoppingTime up p ∈ Ioi s ∧ rssaStoppingMark p = i} := by
      ext p; simp only [mem_setOf_eq, mem_Ioi, Option.some.injEq, Fin.ext_iff]
    rw [he, rssa_stopping_input_marked_law rr lo up (by simp [rr, hn]) hl hbl hA hB hAB i
      (Ioi s) measurableSet_Ioi, exponential_measure_tail _ _ hA hs,
      ← ENNReal.ofReal_mul (div_nonneg ((hbl i.val (by simp [rr, hn])).1.trans
        (hbl i.val (by simp [rr, hn])).2.1) hA.le)]
  rw [htail (t + δ) (by linarith), htail (t - δ) (by linarith)] at h
  exact h

end JumpProcessesLean.Proofs
