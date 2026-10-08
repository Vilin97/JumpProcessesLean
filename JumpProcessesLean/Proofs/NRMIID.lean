import JumpProcessesLean.Proofs.DirectIID

/-!
# Next Reaction Method on IID streams

The NRM implementation consumes one exponential for every channel that needs a fresh
clock: active channels at initialization, the fired channel and reactivated channels
after each event. Inactive and rescaled channels consume nothing. The probability
proof uses complete primitive rows with independent ghost coordinates; here every
fresh coordinate is read from the exponential stream and every unused coordinate from
the otherwise unused uniform stream. The rows are therefore exactly IID.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- Stream coordinates of one primitive row: fresh channels read consecutive
exponential-source draws, all other channels their own uniform slot. -/
def nrmRowIndex : (m : ℕ) → (Fin m → Bool) → ℕ → ℕ → Fin m → ℕ ⊕ ℕ
  | 0, _, _, _ => fun j => Fin.elim0 j
  | m + 1, f, a, b => Fin.cons (if f 0 then .inr b else .inl a)
      (nrmRowIndex m (fun j => f j.succ) (a + 1) (if f 0 then b + 1 else b))

/-- Number of fresh channels in a row. -/
def freshCount : (m : ℕ) → (Fin m → Bool) → ℕ
  | 0, _ => 0
  | m + 1, f => (if f 0 then 1 else 0) + freshCount m (fun j => f j.succ)

lemma freshCount_le : ∀ (m : ℕ) (f : Fin m → Bool), freshCount m f ≤ m
  | 0, _ => le_refl 0
  | m + 1, f => by
    have h := freshCount_le m (fun j => f j.succ)
    simp only [freshCount]
    split_ifs <;> omega

lemma nrmRowIndex_bounds : ∀ (m : ℕ) (f : Fin m → Bool) (a b : ℕ) (j : Fin m),
    (∃ i, nrmRowIndex m f a b j = .inl i ∧ a ≤ i ∧ i < a + m) ∨
      (∃ i, nrmRowIndex m f a b j = .inr i ∧ b ≤ i ∧ i < b + freshCount m f)
  | 0, _, _, _, j => Fin.elim0 j
  | m + 1, f, a, b, j => by
    cases j using Fin.cases with
    | zero =>
      by_cases h0 : f 0 = true
      · right
        exact ⟨b, by simp [nrmRowIndex, h0], le_refl b, by simp [freshCount, h0]⟩
      · left
        exact ⟨a, by simp [nrmRowIndex, h0], le_refl a, by omega⟩
    | succ j =>
      rcases nrmRowIndex_bounds m (fun j => f j.succ) (a + 1) (if f 0 then b + 1 else b) j with
        ⟨i, hi, h1, h2⟩ | ⟨i, hi, h1, h2⟩
      · left
        exact ⟨i, by simp [nrmRowIndex, hi], by omega, by omega⟩
      · right
        refine ⟨i, by simp [nrmRowIndex, hi], ?_, ?_⟩
        · split_ifs at h1 <;> omega
        · simp only [freshCount]
          split_ifs at h2 ⊢ <;> omega

lemma nrmRowIndex_injective : ∀ (m : ℕ) (f : Fin m → Bool) (a b : ℕ),
    Function.Injective (nrmRowIndex m f a b)
  | 0, _, _, _ => fun j => Fin.elim0 j
  | m + 1, f, a, b => by
    have htail := nrmRowIndex_injective m (fun j => f j.succ) (a + 1) (if f 0 then b + 1 else b)
    have hhead : ∀ y : Fin m, nrmRowIndex (m + 1) f a b 0 ≠ nrmRowIndex (m + 1) f a b y.succ := by
      intro y hxy
      rcases nrmRowIndex_bounds m (fun j => f j.succ) (a + 1) (if f 0 then b + 1 else b) y with
        ⟨i, hi, h1, _⟩ | ⟨i, hi, h1, _⟩
      · simp only [nrmRowIndex, Fin.cons_zero, Fin.cons_succ, hi] at hxy
        by_cases h0 : f 0 = true
        · simp [h0] at hxy
        · simp only [h0, Bool.false_eq_true, ite_false, Sum.inl.injEq] at hxy
          omega
      · simp only [nrmRowIndex, Fin.cons_zero, Fin.cons_succ, hi] at hxy
        by_cases h0 : f 0 = true
        · simp only [h0, ite_true, Sum.inr.injEq] at hxy h1
          omega
        · simp [h0] at hxy
    intro x y hxy
    cases x using Fin.cases with
    | zero =>
      cases y using Fin.cases with
      | zero => rfl
      | succ y => exact absurd hxy (hhead y)
    | succ x =>
      cases y using Fin.cases with
      | zero => exact absurd hxy.symm (hhead x)
      | succ y =>
        simp only [nrmRowIndex, Fin.cons_succ] at hxy
        rw [htail hxy]

/-- The fresh-clock pattern used by the native full-graph update. -/
noncomputable def freshPattern {m : ℕ} (old new : Fin m → ℝ) (index fired : ℕ) : Fin m → Bool :=
  fun j => nrmFresh (old j) (new j) (index + j.val) fired

lemma nrmFreshExponentials_succ {m : ℕ} (old new u : Fin (m + 1) → ℝ) (index fired : ℕ) :
    nrmFreshExponentials old new u index fired =
      (if nrmFresh (old 0) (new 0) index fired then [-log (u 0)] else []) ++
        nrmFreshExponentials (fun j => old j.succ) (fun j => new j.succ)
          (fun j => u j.succ) (index + 1) fired := by
  unfold nrmFreshExponentials
  rw [List.ofFn_succ]
  cases h : nrmFresh (old 0) (new 0) index fired <;>
    simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma ofFn_eq_range_map {α : Type} (b : ℕ) (g : ℕ → α) :
    List.ofFn (fun i : Fin b => g i) = (List.range b).map g := by
  apply List.ext_getElem <;> simp

/-- The exponentials actually consumed from a row are consecutive stream draws. -/
lemma nrmFreshExponentials_row : ∀ (m : ℕ) (old new : Fin m → ℝ) (index fired a b : ℕ)
    (ω : Streams),
    nrmFreshExponentials old new
      (fun j => ω (nrmRowIndex m (freshPattern old new index fired) a b j)) index fired =
      (List.range (freshCount m (freshPattern old new index fired))).map
        (fun r => -log (ω (.inr (b + r))))
  | 0, _, _, _, _, _, _, _ => by simp [nrmFreshExponentials, freshCount]
  | m + 1, old, new, index, fired, a, b, ω => by
    rw [nrmFreshExponentials_succ]
    have hpat : freshPattern (fun j => old j.succ) (fun j => new j.succ) (index + 1) fired =
        fun j => freshPattern old new index fired j.succ := by
      funext j
      simp [freshPattern, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
    have htail := nrmFreshExponentials_row m (fun j => old j.succ) (fun j => new j.succ)
      (index + 1) fired (a + 1)
      (if freshPattern old new index fired 0 then b + 1 else b) ω
    rw [hpat] at htail
    have hu : (fun j : Fin m => ω (nrmRowIndex (m + 1) (freshPattern old new index fired) a b j.succ)) =
        (fun j => ω (nrmRowIndex m (fun j => freshPattern old new index fired j.succ) (a + 1)
          (if freshPattern old new index fired 0 then b + 1 else b) j)) := by
      funext j
      simp [nrmRowIndex]
    have hu' : (fun j : Fin m => (fun j => ω (nrmRowIndex (m + 1) (freshPattern old new index fired)
        a b j)) j.succ) = (fun j => ω (nrmRowIndex m (fun j => freshPattern old new index fired j.succ)
          (a + 1) (if freshPattern old new index fired 0 then b + 1 else b) j)) := hu
    rw [hu', htail]
    by_cases h0 : freshPattern old new index fired 0 = true
    · have h0' : nrmFresh (old 0) (new 0) index fired = true := by
        simpa [freshPattern] using h0
      simp only [h0', ite_true, h0, freshCount]
      rw [Nat.add_comm 1, List.range_succ_eq_map]
      simp [nrmRowIndex, h0, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
    · have h0' : nrmFresh (old 0) (new 0) index fired = false := by
        simpa [freshPattern] using h0
      simp only [h0', Bool.false_eq_true, ite_false, List.nil_append, h0, freshCount, zero_add]

/-- One primitive NRM row. -/
noncomputable def nrmRowReader {m : ℕ} (f : Fin m → Bool) : StreamReader (Fin m → ℝ) where
  read ω := fun j => ω (nrmRowIndex m f 0 0 j)
  usedU _ := m
  usedV _ := freshCount m f
  good := univ
  measurable_read := by fun_prop
  measurable_usedU := measurable_const
  measurable_usedV := measurable_const
  measurableSet_good := MeasurableSet.univ
  ae_good := Filter.Eventually.of_forall (fun _ => trivial)
  determined := by
    intro ω _ ω' h
    refine ⟨trivial, ?_, rfl, rfl⟩
    funext j
    rcases nrmRowIndex_bounds m f 0 0 j with ⟨i, hi, _, h2⟩ | ⟨i, hi, _, h2⟩
    · rw [hi]
      have := congrFun (congrArg Prod.fst h) ⟨i, by omega⟩
      simpa [streamsTake] using this
    · rw [hi]
      have := congrFun (congrArg Prod.snd h) ⟨i, by omega⟩
      simpa [streamsTake] using this

theorem nrmRowReader_law {m : ℕ} (f : Fin m → Bool) :
    iidStreams.map (nrmRowReader f).read = Measure.pi (fun _ : Fin m => unitUniform) := by
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ⊕ ℕ => unitUniform)
    (nrmRowIndex_injective m f 0 0)
  rw [Measure.infinitePi_eq_pi (fun _ : Fin m => unitUniform)] at h
  exact h

/-! ### Primitive path measure as a restricted IID product -/

/-- Unrestricted IID primitive rows. -/
noncomputable def nrmRawFreeLaw (n K : ℕ) : Measure (NRMRawInput n K) :=
  (Measure.pi (fun _ : Fin (n + 1) => unitUniform)).prod
    (rawWordLaw (fun _ => Measure.pi (fun _ : Fin (n + 1) => unitUniform)) K)

instance nrmRawFreeLaw_finite (n K : ℕ) : IsFiniteMeasure (nrmRawFreeLaw n K) := by
  unfold nrmRawFreeLaw
  let : IsFiniteMeasure (rawWordLaw (fun _ => Measure.pi (fun _ : Fin (n + 1) => unitUniform)) K) :=
    rawWordLaw_finite _ (fun _ => inferInstance) K
  infer_instance

lemma nrmRawFreeLaw_succ (n K : ℕ) :
    ((nrmRawFreeLaw n K).prod (Measure.pi (fun _ : Fin (n + 1) => unitUniform))).map nrmRawExtend =
      nrmRawFreeLaw n (K + 1) := by
  let U := Measure.pi (fun _ : Fin (n + 1) => unitUniform)
  let R := rawWordLaw (fun _ => U) K
  let : IsFiniteMeasure R := rawWordLaw_finite _ (fun _ => inferInstance) K
  have hcomp : (nrmRawExtend : NRMRawInput n K × (Fin (n + 1) → ℝ) → NRMRawInput n (K + 1)) =
      (Prod.map id rawWordExtend) ∘ MeasurableEquiv.prodAssoc := by
    funext p
    rfl
  unfold nrmRawFreeLaw
  rw [hcomp, ← Measure.map_map (measurable_id.prodMap (measurable_rawWordExtend K))
    (MeasurableEquiv.measurable _), (measurePreserving_prodAssoc U R U).map_eq,
    ← Measure.map_prod_map _ _ measurable_id (measurable_rawWordExtend K), Measure.map_id]
  rfl

lemma uniform_vector_compl_null {n : ℕ} :
    Measure.pi (fun _ : Fin (n + 1) => unitUniform) {u | ∀ j, u j ∈ Ioo 0 1}ᶜ = 0 :=
  ae_iff.mp uniform_vector_ae_mem

/-- The recursive primitive NRM word measure is the IID primitive product restricted
to its strict native winner branch. -/
theorem nrmRawPathLaw_eq_restrict {n : ℕ} (rates : ℕ → Fin (n + 1) → ℝ)
    (marks : ℕ → Fin (n + 1)) (K : ℕ) :
    nrmRawPathLaw rates marks K = (nrmRawFreeLaw n K).restrict {p | NRMRawGood rates marks K p} := by
  induction K with
  | zero =>
    have hfree : nrmRawFreeLaw n 0 = (Measure.pi (fun _ : Fin (n + 1) => unitUniform)).map
        (fun u => (u, fun j : Fin 0 => Fin.elim0 j)) := by
      unfold nrmRawFreeLaw
      rw [rawWordLaw, Measure.prod_dirac]
    rw [hfree, nrmRawPathLaw, Measure.restrict_map (by fun_prop) (measurable_NRMRawGood rates marks 0)]
    congr 1
    refine (Measure.restrict_eq_self_of_ae_mem ?_).symm
    filter_upwards [uniform_vector_ae_mem] with u hu
    exact hu
  | succ K ih =>
    have hS : MeasurableSet {p : NRMRawInput n K × (Fin (n + 1) → ℝ) |
        ((nrmRawHistory rates marks K p.1).2, p.2) ∈ maskedStepBranch (rates K) (marks K)} := by
      apply MeasurableSet.preimage (by unfold maskedStepBranch; measurability)
      exact (measurable_nrmRawHistory rates marks K).snd.comp measurable_fst |>.prodMk measurable_snd
    rw [nrmRawPathLaw, ih, ← nrmRawFreeLaw_succ,
      Measure.restrict_map (measurable_nrmRawExtend n K) (measurable_NRMRawGood rates marks (K + 1))]
    congr 1
    rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_restrict hS]
    apply Measure.restrict_congr_set
    -- The only difference is the null event that a fresh coordinate is an endpoint.
    have hnull : ((nrmRawFreeLaw n K).prod (Measure.pi (fun _ : Fin (n + 1) => unitUniform)))
        (univ ×ˢ {u | ∀ j, u j ∈ Ioo 0 1}ᶜ) = 0 := by
      rw [Measure.prod_prod, uniform_vector_compl_null, mul_zero]
    have hcover : ({p : NRMRawInput n K × (Fin (n + 1) → ℝ) |
          ((nrmRawHistory rates marks K p.1).2, p.2) ∈ maskedStepBranch (rates K) (marks K)} ∩
          {p | NRMRawGood rates marks K p} ×ˢ univ) \ (nrmRawExtend ⁻¹'
            {p | NRMRawGood rates marks (K + 1) p}) ⊆ univ ×ˢ {u | ∀ j, u j ∈ Ioo 0 1}ᶜ := by
      rintro ⟨h, row⟩ ⟨⟨hb, hg, -⟩, hn⟩
      refine ⟨mem_univ _, ?_⟩
      intro hu
      exact hn ⟨hg, hu, hb⟩
    have hsub : nrmRawExtend ⁻¹' {p | NRMRawGood rates marks (K + 1) p} ⊆
        {p : NRMRawInput n K × (Fin (n + 1) → ℝ) |
          ((nrmRawHistory rates marks K p.1).2, p.2) ∈ maskedStepBranch (rates K) (marks K)} ∩
          {p | NRMRawGood rates marks K p} ×ˢ univ := by
      rintro ⟨h, row⟩ hp
      exact ⟨hp.2.2, hp.1, mem_univ _⟩
    exact (ae_le_set.mpr (measure_mono_null hcover hnull)).antisymm hsub.eventuallyLE

/-! ### Native NRM execution with an arbitrary unread tape -/

theorem nrm_active_schedule_concrete_run_from {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin n → ℝ) (marks : Nat → Fin n)
    (c : Nat → Fin n → ℝ) (fresh : Nat → Fin n → ℝ) (start : ℝ)
    (hr : ∀ k j, 0 ≤ rates k j) (hu : ∀ k j, fresh k j ∈ Ioo 0 1)
    (hm : ∀ k, model.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, model.transition (states k) (marks k).val = .ok (states (k + 1)))
    (hrec : ∀ k, 0 < ∑ j, rates k j → ∀ j, 0 < rates (k + 1) j →
      c (k + 1) j = maskedResidual (rates k) (rates (k + 1)) (marks k) (c k) (fresh k) j)
    (limit : Nat) (hw : ∀ k, k ≤ limit → 0 < ∑ j, rates k j →
      0 < rates k (marks k) ∧ 0 < c k (marks k) ∧
      ∀ j, j ≠ marks k → 0 < rates k j → c k (marks k) < c k j)
    (us es : List ℝ) (k fuel maxProposals : Nat) (hlen : k + fuel ≤ limit) :
    let times := nrmScheduleTime c marks start
    ConcreteRun realArithmetic (tapeSource ℝ) model .nrm maxProposals fuel (states k) (times k)
      ⟨us, nrmScheduleTape rates marks fresh k fuel ++ es⟩
      (some (absoluteCache (rates k) (c k) (times k)))
      (nrmScheduleEvents rates c marks times k fuel) := by
  dsimp only
  let times := nrmScheduleTime c marks start
  induction fuel generalizing k with
  | zero =>
    rw [nrmScheduleEvents]
    by_cases hA : 0 < ∑ j, rates k j
    · rw [if_pos hA]
      apply ConcreteRun.budget
      have hwk := hw k (by omega) hA
      dsimp only [sampleEvent]
      rw [nrm_absolute_next (rates k) (c k) (times k) (marks k) hwk.1 hwk.2.2]
      rfl
    · rw [if_neg hA]
      apply ConcreteRun.absorb
      have hn : ∀ j, ¬0 < rates k j := by
        intro j hj
        exact hA (lt_of_lt_of_le hj (Finset.single_le_sum (fun l _ => hr k l) (Finset.mem_univ j)))
      dsimp only [sampleEvent]
      rw [nrm_absolute_absorbing _ _ _ hn]
  | succ fuel ih =>
    rw [nrmScheduleEvents]
    by_cases hA : 0 < ∑ j, rates k j
    · rw [if_pos hA]
      have hwk := hw k (by omega) hA
      apply ConcreteRun.next (newState := states (k + 1))
          (newCache := some (absoluteCache (rates (k + 1)) (c (k + 1)) (times (k + 1))))
          (newRng := ⟨us, nrmScheduleTape rates marks fresh (k + 1) fuel ++ es⟩)
      · dsimp only [sampleEvent]
        rw [nrm_absolute_next (rates k) (c k) (times k) (marks k) hwk.1 hwk.2.2]
        rfl
      · exact hs k
      · dsimp only [refreshCache]
        rw [hm (k + 1)]
        simp only [Array.size_ofFn]
        have hmin : ∀ j, 0 < rates k j → c k (marks k) ≤ c k j := by
          intro j hj
          by_cases he : j = marks k
          · simp [he]
          · exact (hwk.2.2 j he hj).le
        have htime : nrmScheduleTime (c) marks start (k + 1) =
            nrmScheduleTime (c) marks start k + c k (marks k) := rfl
        rw [htime, nrmScheduleTape, List.append_assoc,
          nrm_absolute_update_executes _ _ _ _ (hr (k + 1)) (hu k)
          (times k) (marks k) hmin us (nrmScheduleTape rates marks fresh (k + 1) fuel ++ es)]
        rw [absoluteCache_active_ext (rates (k + 1))
          (maskedResidual (rates k) (rates (k + 1)) (marks k) (c k) (fresh k)) (c (k + 1))
          (times k + c k (marks k)) (fun j hj => (hrec k hA j hj).symm)]
        rfl
      · exact ih (k + 1) (by omega)
    · rw [if_neg hA]
      apply ConcreteRun.absorb
      have hn : ∀ j, ¬0 < rates k j := by
        intro j hj
        exact hA (lt_of_lt_of_le hj (Finset.single_le_sum (fun l _ => hr k l) (Finset.mem_univ j)))
      dsimp only [sampleEvent]
      rw [nrm_absolute_absorbing _ _ _ hn]

/-- Pointwise native NRM execution on a valid primitive branch, followed by any
unread tape. Probability completions at absorbing states are never executed. -/
theorem nrm_completed_driver_executes_from {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (hr : ∀ l j, 0 ≤ rates l j)
    (hm : ∀ l, model.rates (states l) = Array.ofFn (rates l))
    (hs : ∀ l, model.transition (states l) (marks l).val = .ok (states (l + 1)))
    (start horizon : ℝ) (hstart : start < horizon) (fuel maxProposals : Nat) (saveEvents : Bool)
    (p : NRMRawInput n (fuel + 1))
    (hp : NRMRawGood (fun l => completedRates (rates l)) marks (fuel + 1) p) (us es : List ℝ) :
    observeRun (simulate realArithmetic (tapeSource ℝ) model .nrm (states 0) start horizon
      ⟨us, nrmFreshExponentials (fun _ => 0) (rates 0) p.1 0 0 ++
        (nrmScheduleTape rates marks (nrmRawFresh p) 0 fuel ++ es)⟩ fuel saveEvents maxProposals) =
    holdingSimulationObservation model states rates marks start horizon fuel saveEvents
      (nrmRawHistory (fun l => completedRates (rates l)) marks (fuel + 1) p).1 := by
  let completed := fun l => completedRates (rates l)
  obtain ⟨hi, hu⟩ := nrm_raw_schedule_uniforms completed marks p hp
  let c := nrmScheduleCache completed marks p.1 (nrmRawFresh p)
  let times := nrmScheduleTime c marks start
  have hrec : ∀ k, 0 < ∑ j, rates k j → ∀ j, 0 < rates (k + 1) j →
      c (k + 1) j = maskedResidual (rates k) (rates (k + 1)) (marks k) (c k) (nrmRawFresh p k) j := by
    intro k hA j hj
    have hB : 0 < ∑ j, rates (k + 1) j :=
      lt_of_lt_of_le hj (Finset.single_le_sum (fun l _ => hr (k + 1) l) (Finset.mem_univ j))
    change maskedResidual (completedRates (rates k)) (completedRates (rates (k + 1)))
      (marks k) (c k) (nrmRawFresh p k) j = _
    simp only [completedRates, hA, hB, ite_true]
  have hwin : ∀ k, k ≤ fuel → 0 < ∑ j, rates k j →
      0 < rates k (marks k) ∧ 0 < c k (marks k) ∧
        ∀ j, j ≠ marks k → 0 < rates k j → c k (marks k) < c k j := by
    intro k hk hA
    have h := nrm_raw_schedule_winners completed marks p hp k (by omega)
    simpa only [c, completed, completedRates, hA, ite_true] using h
  have hrun : observeRun (simulate realArithmetic (tapeSource ℝ) model .nrm (states 0) start horizon
      ⟨us, nrmFreshExponentials (fun _ => 0) (rates 0) p.1 0 0 ++
        (nrmScheduleTape rates marks (nrmRawFresh p) 0 fuel ++ es)⟩ fuel saveEvents maxProposals) =
      replayEvents realArithmetic model horizon saveEvents fuel (states 0) start 0 #[(start, states 0)]
        (nrmScheduleEvents rates c marks times 0 fuel) := by
    apply simulate_refines_replay (tapeSource ℝ) model .nrm (states 0) start horizon hstart _
      ⟨us, nrmScheduleTape rates marks (nrmRawFresh p) 0 fuel ++ es⟩
      (some (absoluteCache (rates 0) (c 0) start)) fuel maxProposals saveEvents _
    · unfold initializeCache
      rw [hm 0, nrmInitialize_masked_executes _ _ (hr 0) hi start us
        (nrmScheduleTape rates marks (nrmRawFresh p) 0 fuel ++ es)]
      have he : (fun j => if 0 < rates 0 j then some (start + exponentialClock (rates 0 j) (p.1 j)) else none) =
          (fun j => if 0 < rates 0 j then some (start + c 0 j) else none) := by
        funext j
        by_cases hj : 0 < rates 0 j
        · have hA : 0 < ∑ l, rates 0 l :=
            lt_of_lt_of_le hj (Finset.single_le_sum (fun l _ => hr 0 l) (Finset.mem_univ j))
          simp [c, nrmScheduleCache, completed, completedRates, hA, hj, ghostRate_of_positive hj]
        · simp [hj]
      simp only [he, absoluteCache, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · exact nrm_active_schedule_concrete_run_from model states rates marks c (nrmRawFresh p) start
        hr hu hm hs hrec fuel hwin us es 0 fuel maxProposals (by omega)
  rw [hrun]
  unfold holdingSimulationObservation
  have he := schedule_events_times_congr rates c
    (holdingSchedule (nrmRawHistory completed marks (fuel + 1) p).1)
    marks _ _ (fuel + 1)
    (fun l hl => holding_schedule_times completed marks p start l hl) 0 fuel (by omega)
  rw [he]

/-! ### Reading primitive NRM rows from the IID streams -/

/-- Initialization row: active channels read exponential-source draws. -/
noncomputable def nrmInitReader {n : ℕ} (rates0 : Fin (n + 1) → ℝ) :
    StreamReader (Fin (n + 1) → ℝ) :=
  nrmRowReader (freshPattern (fun _ => 0) rates0 0 0)

/-- Update rows along a reaction word. -/
noncomputable def nrmStepReaders {n : ℕ} (rr : ℕ → Fin (n + 1) → ℝ) (marks : ℕ → Fin (n + 1)) :
    ℕ → StreamReader (Fin (n + 1) → ℝ) :=
  fun l => nrmRowReader (freshPattern (rr l) (rr (l + 1)) 0 (marks l).val)

/-- Exponential-source draws consumed by one update row. -/
noncomputable def nrmStepCount {n : ℕ} (rr : ℕ → Fin (n + 1) → ℝ) (marks : ℕ → Fin (n + 1))
    (l : ℕ) : ℕ :=
  freshCount (n + 1) (freshPattern (rr l) (rr (l + 1)) 0 (marks l).val)

/-- Sequentially read primitive NRM input along a reaction word. -/
noncomputable def nrmParse {n : ℕ} (rr : ℕ → Fin (n + 1) → ℝ) (marks : ℕ → Fin (n + 1)) (K : ℕ)
    (ω : Streams) : NRMRawInput n K :=
  ((nrmInitReader (rr 0)).read ω,
    (readerParse (nrmStepReaders rr marks) K ((nrmInitReader (rr 0)).rest ω)).1)

lemma measurable_nrmParse {n : ℕ} (rr : ℕ → Fin (n + 1) → ℝ) (marks : ℕ → Fin (n + 1)) (K : ℕ) :
    Measurable (nrmParse rr marks K) :=
  (nrmInitReader (rr 0)).measurable_read.prodMk
    ((measurable_readerParse _ K).fst.comp (nrmInitReader (rr 0)).measurable_rest)

theorem nrmParse_law {n : ℕ} (rr : ℕ → Fin (n + 1) → ℝ) (marks : ℕ → Fin (n + 1)) (K : ℕ) :
    iidStreams.map (nrmParse rr marks K) = nrmRawFreeLaw n K := by
  let r0 := nrmInitReader (rr 0)
  have hcomp : nrmParse rr marks K =
      (Prod.map id (fun ω' => (readerParse (nrmStepReaders rr marks) K ω').1)) ∘
        (fun ω => (r0.read ω, r0.rest ω)) := rfl
  have hrows : iidStreams.map (fun ω' => (readerParse (nrmStepReaders rr marks) K ω').1) =
      rawWordLaw (fun _ => Measure.pi (fun _ : Fin (n + 1) => unitUniform)) K := by
    have h := congrArg (fun μ => μ.map Prod.fst) (readerParse_law (nrmStepReaders rr marks) K)
    simp only [Measure.map_map measurable_fst (measurable_readerParse _ K)] at h
    rw [Measure.map_fst_prod, measure_univ, one_smul] at h
    have hp : (fun ω' => (readerParse (nrmStepReaders rr marks) K ω').1) =
        Prod.fst ∘ readerParse (nrmStepReaders rr marks) K := rfl
    rw [hp, h]
    simp only [nrmStepReaders, nrmRowReader_law]
  rw [hcomp, ← Measure.map_map (measurable_id.prodMap (measurable_readerParse _ K).fst)
    (r0.measurable_read.prodMk r0.measurable_rest), r0.regenerate,
    ← Measure.map_prod_map _ _ measurable_id (measurable_readerParse _ K).fst, Measure.map_id, hrows]
  simp only [r0, nrmInitReader, nrmRowReader_law]
  rfl

lemma nrmParse_fresh {n : ℕ} (rr : ℕ → Fin (n + 1) → ℝ) (marks : ℕ → Fin (n + 1)) (K : ℕ)
    (ω : Streams) (l : ℕ) (hl : l < K) :
    nrmRawFresh (nrmParse rr marks K ω) l =
      (nrmStepReaders rr marks l).read
        (streamsDrop (∑ i ∈ Finset.range l, (n + 1)) (∑ i ∈ Finset.range l, nrmStepCount rr marks i)
          ((nrmInitReader (rr 0)).rest ω)) := by
  simp only [nrmRawFresh, hl, dite_true, nrmParse]
  rw [readerParse_chron _ K _ l hl,
    readerParse_rest_const (nrmStepReaders rr marks) (fun _ => n + 1) (nrmStepCount rr marks)
      (fun _ _ => rfl) (fun _ _ => rfl)]

lemma nrmParse_schedule_tape {n : ℕ} (rr : ℕ → Fin (n + 1) → ℝ) (marks : ℕ → Fin (n + 1)) (K : ℕ)
    (ω : Streams) (c0 : ℕ) (hω : (nrmInitReader (rr 0)).rest ω = streamsDrop (n + 1) c0 ω) :
    ∀ count k, k + count ≤ K →
      nrmScheduleTape rr marks (nrmRawFresh (nrmParse rr marks K ω)) k count =
        (List.range (∑ i ∈ Finset.range count, nrmStepCount rr marks (k + i))).map
          (fun r => -log (ω (.inr (c0 + (∑ i ∈ Finset.range k, nrmStepCount rr marks i) + r)))) := by
  intro count
  induction count with
  | zero => intro k _; simp [nrmScheduleTape]
  | succ count ih =>
    intro k hk
    rw [nrmScheduleTape, ih (k + 1) (by omega), nrmParse_fresh rr marks K ω k (by omega), hω,
      streamsDrop_drop]
    have hrow := nrmFreshExponentials_row (n + 1) (rr k) (rr (k + 1)) 0 (marks k).val 0 0
      (streamsDrop (n + 1 + ∑ i ∈ Finset.range k, (n + 1))
        (c0 + ∑ i ∈ Finset.range k, nrmStepCount rr marks i) ω)
    simp only [nrmStepReaders, nrmRowReader] at hrow ⊢
    rw [hrow]
    have hsum : ∑ i ∈ Finset.range (count + 1), nrmStepCount rr marks (k + i) =
        nrmStepCount rr marks k + ∑ i ∈ Finset.range count, nrmStepCount rr marks (k + 1 + i) := by
      rw [Finset.sum_range_succ', add_comm]
      simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    have hprefix : ∑ i ∈ Finset.range (k + 1), nrmStepCount rr marks i =
        ∑ i ∈ Finset.range k, nrmStepCount rr marks i + nrmStepCount rr marks k :=
      Finset.sum_range_succ _ _
    rw [hsum, hprefix, List.range_add, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro r _
      simp only [streamsDrop, Sum.map_inr, nrmStepCount, zero_add]
    · apply List.map_congr_left
      intro r _
      simp only [Function.comp_apply, nrmStepCount]
      congr 4
      omega

lemma nrmScheduleCache_congr {n : ℕ} (rates rates' : ℕ → Fin n → ℝ) (marks marks' : ℕ → Fin n)
    (u : Fin n → ℝ) (fresh fresh' : ℕ → Fin n → ℝ) (l : ℕ)
    (hr : ∀ m, m ≤ l → rates m = rates' m) (hm : ∀ m, m < l → marks m = marks' m)
    (hf : ∀ m, m < l → fresh m = fresh' m) :
    nrmScheduleCache rates marks u fresh l = nrmScheduleCache rates' marks' u fresh' l := by
  induction l with
  | zero => simp only [nrmScheduleCache, hr 0 (le_refl 0)]
  | succ l ih =>
    simp only [nrmScheduleCache]
    rw [ih (fun m hm' => hr m (by omega)) (fun m hm' => hm m (by omega)) (fun m hm' => hf m (by omega)),
      hr l (by omega), hr (l + 1) (le_refl _), hm l (by omega), hf l (by omega)]

lemma nrmParse_init_tape {n : ℕ} (rr : ℕ → Fin (n + 1) → ℝ) (marks : ℕ → Fin (n + 1)) (K : ℕ)
    (ω : Streams) :
    nrmFreshExponentials (fun _ => 0) (rr 0) (nrmParse rr marks K ω).1 0 0 =
      (List.range (freshCount (n + 1) (freshPattern (fun _ => 0) (rr 0) 0 0))).map
        (fun r => -log (ω (.inr r))) := by
  have h := nrmFreshExponentials_row (n + 1) (fun _ => 0) (rr 0) 0 0 0 0 ω
  simp only [zero_add] at h
  exact h

/-- The actual NRM simulation on IID streams, with persistent absolute clocks,
inactive channels and fresh/rescaled updates, has the target stopped law. -/
theorem nrm_iid_simulation_law {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper)
    (initial : σ) (start horizon : ℝ) (hstart : start < horizon)
    (fuel cap : Nat) (saveEvents : Bool) (a b : Nat) (hb : (n + 1) * (fuel + 1) ≤ b)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts => observable (holdingSimulationObservation model states
        (fun l => rates (states l)) marks start horizon fuel saveEvents ts))) :
    iidStreams.map (fun ω => observable (observeRun (simulate realArithmetic (tapeSource ℝ)
      model .nrm initial start horizon (streamTape a b ω) fuel saveEvents cap))) =
    targetSimulationLaw model transition rates initial start horizon fuel saveEvents observable := by
  set K := fuel + 1 with hK
  let states : (Fin K → Fin (n + 1)) → Nat → σ := fun w =>
    stateAlongWord transition initial (extendMarks w)
  let rr : (Fin K → Fin (n + 1)) → Nat → Fin (n + 1) → ℝ := fun w l => rates (states w l)
  let cr : (Fin K → Fin (n + 1)) → Nat → Fin (n + 1) → ℝ := fun w l => completedRates (rr w l)
  let parse : (Fin K → Fin (n + 1)) → Streams → NRMRawInput n K := fun w =>
    nrmParse (rr w) (extendMarks w) K
  have hparse : ∀ w, Measurable (parse w) := fun w => measurable_nrmParse _ _ K
  let E : (Fin K → Fin (n + 1)) → Set Streams := fun w =>
    parse w ⁻¹' {p | NRMRawGood (cr w) (extendMarks w) K p}
  have hE : ∀ w, MeasurableSet (E w) := fun w =>
    hparse w (measurable_NRMRawGood _ _ K)
  have hbranch : ∀ w, (iidStreams.restrict (E w)).map (parse w) =
      nrmRawPathLaw (cr w) (extendMarks w) K := by
    intro w
    rw [← Measure.restrict_map (hparse w) (measurable_NRMRawGood _ _ K), nrmParse_law,
      nrmRawPathLaw_eq_restrict]
  have hcr : ∀ w l j, 0 ≤ cr w l j := fun w l =>
    completedRates_nonnegative _ (fun j => C.nonnegative _ j)
  have hholding : ∀ w, (nrmRawPathLaw (cr w) (extendMarks w) K).map
      (fun p => (nrmRawHistory (cr w) (extendMarks w) K p).1) =
      targetWordLaw (cr w) (extendMarks w) K := fun w =>
    nrm_raw_holding_times_law (cr w) (hcr w) (extendMarks w) K
  have hmhist : ∀ w, Measurable (fun p => (nrmRawHistory (cr w) (extendMarks w) K p).1) :=
    fun w => (measurable_nrmRawHistory _ _ K).fst
  -- The words partition the probability space.
  have hmass : ∑ w, iidStreams (E w) = 1 := by
    have hw : ∀ w, iidStreams (E w) = pathWordWeight transition rates initial w := by
      intro w
      have h1 : iidStreams (E w) = ((iidStreams.restrict (E w)).map (parse w)) univ := by
        rw [Measure.map_apply (hparse w) MeasurableSet.univ, preimage_univ,
          Measure.restrict_apply_univ]
      rw [h1, hbranch, ← preimage_univ (f := fun p => (nrmRawHistory (cr w) (extendMarks w) K p).1),
        ← Measure.map_apply (hmhist w) MeasurableSet.univ, hholding,
        target_word_mass _ (fun l => completedRates_positive_total _)]
      unfold pathWordWeight
      apply Finset.prod_congr rfl
      intro q _
      simp only [extendMarks, q.isLt, dite_true, cr, rr, states]
    simp_rw [hw]
    exact path_word_weights_normalize transition rates C.nonnegative K initial
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro w w' hww
    rw [Function.onFun, Set.disjoint_left]
    intro ω hω hω'
    apply hww
    apply words_eq_of_sequential_choice
    intro l hl hprev
    have hmarks : ∀ j, j < l → extendMarks w j = extendMarks w' j :=
      extendMarks_agree w w' l (fun j hj hjK => hprev j hj)
    have hstates : ∀ m, m ≤ l → states w m = states w' m := fun m hm =>
      stateAlongWord_congr transition initial _ _ m (fun j hj => hmarks j (by omega))
    have hrr : ∀ m, m ≤ l → rr w m = rr w' m := fun m hm => by
      simp only [rr, hstates m hm]
    have hcr' : ∀ m, m ≤ l → cr w m = cr w' m := fun m hm => by
      simp only [cr, hrr m hm]
    have hreaders : ∀ m, m < l → nrmStepReaders (rr w) (extendMarks w) m =
        nrmStepReaders (rr w') (extendMarks w') m := by
      intro m hm
      simp only [nrmStepReaders, hrr m (by omega), hrr (m + 1) (by omega), hmarks m hm]
    have hinit : (parse w ω).1 = (parse w' ω).1 := by
      simp only [parse, nrmParse, hrr 0 (Nat.zero_le _)]
    have hrows : ∀ m, m < l → nrmRawFresh (parse w ω) m = nrmRawFresh (parse w' ω) m := by
      intro m hm
      have hmK : m < K := by omega
      simp only [parse]
      rw [nrmParse_fresh _ _ K ω m hmK, nrmParse_fresh _ _ K ω m hmK, hreaders m hm,
        hrr 0 (Nat.zero_le _)]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      simp only [nrmStepCount, Finset.mem_range] at hi ⊢
      rw [hrr i (by omega), hrr (i + 1) (by omega), hmarks i (by omega)]
    have hcache : nrmScheduleCache (cr w) (extendMarks w) (parse w ω).1 (nrmRawFresh (parse w ω)) l =
        nrmScheduleCache (cr w') (extendMarks w') (parse w' ω).1 (nrmRawFresh (parse w' ω)) l := by
      rw [hinit]
      exact nrmScheduleCache_congr _ _ _ _ _ _ _ l hcr' hmarks hrows
    have h1 := nrm_raw_schedule_winners (cr w) (extendMarks w) (parse w ω) hω l hl
    have h2 := nrm_raw_schedule_winners (cr w') (extendMarks w') (parse w' ω) hω' l hl
    rw [hcache, hcr' l (le_refl l)] at h1
    have hmw : extendMarks w l = w ⟨l, hl⟩ := by simp [extendMarks, hl]
    have hmw' : extendMarks w' l = w' ⟨l, hl⟩ := by simp [extendMarks, hl]
    rw [hmw] at h1
    rw [hmw'] at h2
    by_contra hne
    have hlt1 := h1.2.2 (w' ⟨l, hl⟩) (Ne.symm hne) h2.1
    have hlt2 := h2.2.2 (w ⟨l, hl⟩) hne h1.1
    linarith
  -- Pointwise execution of the public driver on each word branch.
  let G : (Fin K → Fin (n + 1)) → Streams → X := fun w ω =>
    observable (holdingSimulationObservation model (states w) (rr w) (extendMarks w) start horizon
      fuel saveEvents ((nrmRawHistory (cr w) (extendMarks w) K (parse w ω)).1))
  have hG : ∀ w, Measurable (G w) := fun w => (hobs w).comp ((hmhist w).comp (hparse w))
  have hFG : ∀ w, ∀ᵐ ω ∂iidStreams, ω ∈ E w →
      observable (observeRun (simulate realArithmetic (tapeSource ℝ) model .nrm initial start
        horizon (streamTape a b ω) fuel saveEvents cap)) = G w ω := by
    intro w
    refine Filter.Eventually.of_forall (fun ω hEw => ?_)
    let c0 := freshCount (n + 1) (freshPattern (fun _ => 0) (rr w 0) 0 0)
    let S := ∑ i ∈ Finset.range fuel, nrmStepCount (rr w) (extendMarks w) i
    have hc0 : c0 ≤ n + 1 := freshCount_le _ _
    have hS : S ≤ (n + 1) * fuel := by
      calc S ≤ ∑ i ∈ Finset.range fuel, (n + 1) :=
            Finset.sum_le_sum (fun i _ => freshCount_le _ _)
        _ = (n + 1) * fuel := by simp [mul_comm]
    have hMb : c0 + S ≤ b := by nlinarith
    obtain ⟨rest, hrest⟩ := Nat.exists_eq_add_of_le hMb
    have hω0 : (nrmInitReader (rr w 0)).rest ω = streamsDrop (n + 1) c0 ω := rfl
    have hsched := nrmParse_schedule_tape (rr w) (extendMarks w) K ω c0 hω0 fuel 0 (by omega)
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add] at hsched
    have htape : streamTape a b ω =
        ⟨List.ofFn (fun i : Fin a => ω (.inl i)),
          nrmFreshExponentials (fun _ => 0) (rr w 0) (parse w ω).1 0 0 ++
            (nrmScheduleTape (rr w) (extendMarks w) (nrmRawFresh (parse w ω)) 0 fuel ++
              (List.range rest).map (fun r => -log (ω (.inr (c0 + S + r)))))⟩ := by
      simp only [streamTape, parse]
      congr 1
      rw [nrmParse_init_tape, hsched, ofFn_eq_range_map b (fun i => -log (ω (.inr i))), hrest,
        List.range_add, List.range_add, List.map_append, List.map_append, List.map_map,
        List.map_map, List.append_assoc]
      rfl
    have hinit : initial = states w 0 := rfl
    simp only [G]
    rw [htape, hinit, nrm_completed_driver_executes_from model (states w) (rr w) (extendMarks w)
      (fun l j => C.nonnegative _ j) (fun l => C.rates_eq _) (fun l => C.transition_eq _ _)
      start horizon hstart fuel cap saveEvents (parse w ω) hEw]
  rw [iid_word_decomposition E hE hdisj hmass _ G hG hFG]
  unfold targetSimulationLaw
  congr 1
  funext w
  have h1 := Measure.map_map (μ := iidStreams.restrict (E w)) (hobs w) ((hmhist w).comp (hparse w))
  have h2 := Measure.map_map (μ := iidStreams.restrict (E w)) (hmhist w) (hparse w)
  rw [← h2, hbranch, hholding] at h1
  exact h1.symm

end JumpProcessesLean.Proofs
