import JumpProcessesLean.Proofs.NRMSimulationLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

def rawWordExtend {γ : Type} {k : Nat} (p : (Fin k → γ) × γ) : Fin (k + 1) → γ :=
  Fin.cases p.2 p.1

lemma measurable_rawWordExtend {γ : Type} [MeasurableSpace γ] (k : Nat) :
    Measurable (@rawWordExtend γ k) := by
  apply Measurable.of_eval
  intro q
  cases q using Fin.cases <;> simp only [rawWordExtend, Fin.cases_zero, Fin.cases_succ] <;> fun_prop

noncomputable def rawWordLaw {γ : Type} [MeasurableSpace γ] (inputs : Nat → Measure γ) :
    (k : Nat) → Measure (Fin k → γ)
  | 0 => Measure.dirac (fun q => Fin.elim0 q)
  | k + 1 => ((rawWordLaw inputs k).prod (inputs k)).map rawWordExtend

lemma rawWordLaw_finite {γ : Type} [MeasurableSpace γ] (inputs : Nat → Measure γ)
    (h : ∀ k, IsFiniteMeasure (inputs k)) (k : Nat) : IsFiniteMeasure (rawWordLaw inputs k) := by
  induction k with
  | zero => unfold rawWordLaw; infer_instance
  | succ k ih =>
    let : IsFiniteMeasure (rawWordLaw inputs k) := ih
    let : IsFiniteMeasure (inputs k) := h k
    unfold rawWordLaw
    infer_instance

noncomputable def rawWordHoldings {γ : Type} (clock : Nat → γ → ℝ) :
    (k : Nat) → (Fin k → γ) → Fin k → ℝ
  | 0, _ => fun q => Fin.elim0 q
  | k + 1, p => prependHoldingTime (rawWordHoldings clock k (Fin.tail p), clock k (p 0))

lemma measurable_rawWordHoldings {γ : Type} [MeasurableSpace γ] (clock : Nat → γ → ℝ)
    (hc : ∀ k, Measurable (clock k)) (k : Nat) : Measurable (rawWordHoldings clock k) := by
  induction k with
  | zero => fun_prop
  | succ k ih =>
    have ht : Measurable (fun p : Fin (k + 1) → γ => Fin.tail p) :=
      Measurable.of_eval (fun i => measurable_pi_apply i.succ)
    exact (measurable_prependHoldingTime k).comp
      ((ih.comp ht).prodMk ((hc k).comp (measurable_pi_apply 0)))

theorem raw_word_holding_law {γ : Type} [MeasurableSpace γ] (inputs : Nat → Measure γ)
    (hfinite : ∀ k, IsFiniteMeasure (inputs k)) (clock : Nat → γ → ℝ)
    (hc : ∀ k, Measurable (clock k)) (k : Nat) :
    (rawWordLaw inputs k).map (rawWordHoldings clock k) =
      independentWordLaw (fun l => (inputs l).map (clock l)) k := by
  induction k with
  | zero => rw [rawWordLaw, Measure.map_dirac]; rfl
  | succ k ih =>
    let : IsFiniteMeasure (rawWordLaw inputs k) := rawWordLaw_finite inputs hfinite k
    let : IsFiniteMeasure (inputs k) := hfinite k
    rw [rawWordLaw, Measure.map_map (measurable_rawWordHoldings clock hc (k + 1))
      (measurable_rawWordExtend k), independentWordLaw, ← ih,
      Measure.map_prod_map _ _ (measurable_rawWordHoldings clock hc k) (hc k),
      Measure.map_map (measurable_prependHoldingTime k)
        ((measurable_rawWordHoldings clock hc k).prodMap (hc k))]
    rfl

def RawWordGood {γ : Type} (good : Nat → γ → Prop) : (k : Nat) → (Fin k → γ) → Prop
  | 0, _ => True
  | k + 1, p => RawWordGood good k (Fin.tail p) ∧ good k (p 0)

lemma measurable_RawWordGood {γ : Type} [MeasurableSpace γ] (good : Nat → γ → Prop)
    (hm : ∀ k, MeasurableSet {p | good k p}) (k : Nat) :
    MeasurableSet {p | RawWordGood good k p} := by
  induction k with
  | zero => simp [RawWordGood]
  | succ k ih =>
    have ht : Measurable (fun p : Fin (k + 1) → γ => Fin.tail p) :=
      Measurable.of_eval (fun i => measurable_pi_apply i.succ)
    exact (ih.preimage ht).inter ((hm k).preimage (measurable_pi_apply 0))

theorem raw_word_good_ae {γ : Type} [MeasurableSpace γ] (inputs : Nat → Measure γ)
    (hfinite : ∀ k, IsFiniteMeasure (inputs k)) (good : Nat → γ → Prop)
    (hm : ∀ k, MeasurableSet {p | good k p}) (hg : ∀ k, ∀ᵐ p ∂inputs k, good k p) (k : Nat) :
    ∀ᵐ p ∂rawWordLaw inputs k, RawWordGood good k p := by
  induction k with
  | zero => exact Filter.Eventually.of_forall (fun _ => trivial)
  | succ k ih =>
    let : IsFiniteMeasure (rawWordLaw inputs k) := rawWordLaw_finite inputs hfinite k
    let : IsFiniteMeasure (inputs k) := hfinite k
    rw [rawWordLaw, ae_map_iff (measurable_rawWordExtend k).aemeasurable (measurable_RawWordGood good hm (k + 1))]
    have hprev := (Measure.quasiMeasurePreserving_fst
      (μ := rawWordLaw inputs k) (ν := inputs k)).tendsto_ae.eventually ih
    have hnext := (Measure.quasiMeasurePreserving_snd
      (μ := rawWordLaw inputs k) (ν := inputs k)).tendsto_ae.eventually (hg k)
    filter_upwards [hprev, hnext] with p hp hq
    exact ⟨hp, hq⟩

lemma raw_word_good_index {γ : Type} (good : Nat → γ → Prop) {k : Nat}
    (p : Fin k → γ) (hg : RawWordGood good k p) (q : Fin k) :
    good (k - 1 - q.val) (p q) := by
  induction k with
  | zero => exact Fin.elim0 q
  | succ k ih =>
    cases q using Fin.cases with
    | zero => simpa using hg.2
    | succ q =>
      have he : k + 1 - 1 - q.succ.val = k - 1 - q.val := by simp only [Fin.val_succ]; omega
      simpa only [he, Fin.tail] using ih (Fin.tail p) hg.1 q

lemma raw_word_holding_index {γ : Type} (clock : Nat → γ → ℝ) {k : Nat}
    (p : Fin k → γ) (q : Fin k) :
    rawWordHoldings clock k p q = clock (k - 1 - q.val) (p q) := by
  induction k with
  | zero => exact Fin.elim0 q
  | succ k ih =>
    cases q using Fin.cases with
    | zero => simp [rawWordHoldings, prependHoldingTime]
    | succ q =>
      have he : k + 1 - 1 - q.succ.val = k - 1 - q.val := by simp only [Fin.val_succ]; omega
      simpa only [rawWordHoldings, prependHoldingTime, Fin.cases_succ, he, Fin.tail] using ih (Fin.tail p) q

def rawChronological {γ : Type} {k : Nat} (fallback : γ) (p : Fin k → γ) (l : Nat) : γ :=
  if h : l < k then p ⟨k - 1 - l, by omega⟩ else fallback

lemma raw_chronological_good {γ : Type} {k : Nat} (fallback : γ) (p : Fin k → γ)
    (good : Nat → γ → Prop) (hg : RawWordGood good k p) (l : Nat) (hl : l < k) :
    good l (rawChronological fallback p l) := by
  have h := raw_word_good_index good p hg ⟨k - 1 - l, by omega⟩
  have he : k - 1 - (k - 1 - l) = l := by omega
  simpa [rawChronological, hl, he] using h

lemma raw_chronological_clock {γ : Type} {k n : Nat} (fallback : γ) (p : Fin k → γ)
    (clock : Nat → γ → ℝ) (l : Nat) (hl : l < k) (i : Fin n) :
    holdingSchedule (n := n) (rawWordHoldings clock k p) l i =
      clock l (rawChronological fallback p l) := by
  have he : k - 1 - (k - 1 - l) = l := by omega
  simp [holdingSchedule, hl, raw_word_holding_index, rawChronological, he]

end JumpProcessesLean.Proofs
