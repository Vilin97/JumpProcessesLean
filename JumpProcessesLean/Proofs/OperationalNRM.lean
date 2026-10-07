import JumpProcessesLean.Proofs.OperationalDirect
import JumpProcessesLean.Proofs.OperationalRace
import JumpProcessesLean.NRM

namespace JumpProcessesLean.Proofs
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- The initialization loop is refined pointwise all the way to inverse-transform clocks. -/
theorem nrmInitializeAux_uniform {n : Nat} (rates u : Fin n → ℝ)
    (hr : ∀ i, 0 < rates i) (hu : ∀ i, u i ∈ Ioo 0 1) (now : ℝ) (us : List ℝ) :
    nrmInitializeAux realArithmetic (tapeSource ℝ) now (List.ofFn rates)
      ⟨us, List.ofFn (fun i => -log (u i))⟩ =
      .ok (List.ofFn (fun i => some (now + exponentialClock (rates i) (u i))), ⟨us, []⟩) := by
  induction n with
  | zero => simp [nrmInitializeAux, List.ofFn_zero]
  | succ n ih =>
    have he : 0 < -log (u 0) := neg_pos.mpr (log_neg (hu 0).1 (hu 0).2)
    have ht : now < now + -log (u 0) / rates 0 := lt_add_of_pos_right _ (div_pos he (hr 0))
    have hd : drawExponential realArithmetic (tapeSource ℝ)
        (⟨us, -log (u 0) :: List.ofFn (fun i : Fin n => -log (u i.succ))⟩ : Tape ℝ) =
      .ok (-log (u 0), ⟨us, List.ofFn (fun i : Fin n => -log (u i.succ))⟩) := by
      simp [drawExponential, tapeSource, realArithmetic, Bind.bind, Except.bind, not_le.mpr (log_neg (hu 0).1 (hu 0).2)]
      rfl
    simp only [List.ofFn_succ, nrmInitializeAux]
    have hi := ih (fun i => rates i.succ) (fun i => u i.succ)
      (fun i => hr i.succ) (fun i => hu i.succ)
    simp only [realArithmetic, exponentialClock] at hd hi ⊢
    simp only [hr 0, decide_true, ite_true, hd, Bind.bind, Except.bind,
      Bool.true_and, ht, Bool.not_true, Bool.false_eq_true, ite_false,
      Pure.pure, Except.pure, hi, exponentialClock]

lemma nrmNextAux_sound (clocks : List ℝ) (index : Nat) (e : Event ℝ)
    (he : nrmNextAux realArithmetic (clocks.map some) index = some e) :
    ∃ (j : Nat) (hj : j < clocks.length), e.reaction = index + j ∧ e.time = clocks[j]'hj ∧
      ∀ t ∈ clocks, e.time ≤ t := by
  induction clocks generalizing index e with
  | nil => simp [nrmNextAux] at he
  | cons t rest ih =>
    simp only [List.map_cons, nrmNextAux] at he
    cases hrest : nrmNextAux realArithmetic (rest.map some) (index + 1) with
    | none =>
      simp only [hrest] at he
      cases he
      have hempty : rest = [] := by
        cases rest with
        | nil => rfl
        | cons s ss =>
          simp only [List.map_cons, nrmNextAux] at hrest
          cases htail : nrmNextAux realArithmetic (ss.map some) (index + 2) with
          | none => simp [show index + 1 + 1 = index + 2 by omega, htail] at hrest
          | some b =>
            simp only [show index + 1 + 1 = index + 2 by omega, htail] at hrest
            split at hrest <;> contradiction
      subst rest
      exact ⟨0, by simp, by simp, rfl, by simp⟩
    | some b =>
      obtain ⟨j, hj, hrx, htime, hmin⟩ := ih (index + 1) b hrest
      simp only [hrest] at he
      simp only [realArithmetic, decide_eq_true_eq] at he
      by_cases htb : t ≤ b.time
      · simp only [htb, ite_true] at he
        cases he
        refine ⟨0, by simp, by simp, rfl, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_refl _
        · exact htb.trans (hmin x hx)
      · simp only [htb, ite_false] at he
        cases he
        refine ⟨j + 1, by simpa using hj, by omega, by simpa using htime, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (lt_of_not_ge htb).le
        · exact hmin x hx

lemma nrmNextAux_unique (clocks : List ℝ) (index i : Nat) (hi : i < clocks.length)
    (hmin : ∀ j : Nat, (hj : j < clocks.length) → j ≠ i → clocks[i] < clocks[j]) :
    nrmNextAux realArithmetic (clocks.map some) index = some ⟨clocks[i], index + i⟩ := by
  have hex : ∀ (xs : List ℝ) (k : Nat), xs ≠ [] → ∃ e,
      nrmNextAux realArithmetic (xs.map some) k = some e := by
    intro xs k hn
    cases xs with
    | nil => exact (hn rfl).elim
    | cons a rest =>
      simp only [List.map_cons, nrmNextAux]
      cases h : nrmNextAux realArithmetic (rest.map some) (k + 1) with
      | none => exact ⟨⟨a, k⟩, rfl⟩
      | some b =>
        by_cases hab : realArithmetic.le a b.time = true
        · exact ⟨⟨a, k⟩, if_pos hab⟩
        · exact ⟨b, if_neg hab⟩
  obtain ⟨e, he⟩ := hex clocks index (by intro h; simp [h] at hi)
  obtain ⟨j, hj, hrx, htime, hle⟩ := nrmNextAux_sound clocks index e he
  have hji : j = i := by
    by_contra h
    have ht := hmin j hj h
    have hm := hle clocks[i] (List.getElem_mem hi)
    rw [htime] at hm
    linarith
  have heq : e = ⟨clocks[i], index + i⟩ := by
    cases e
    simp_all
  simpa [heq] using he

theorem nrmInitialize_uniform_executes {n : Nat} (rates u : Fin n → ℝ)
    (hr : ∀ i, 0 < rates i) (hu : ∀ i, u i ∈ Ioo 0 1) (now : ℝ) :
    nrmInitialize realArithmetic (tapeSource ℝ) (Array.ofFn rates) now
      ⟨[], List.ofFn (fun i => -log (u i))⟩ =
      .ok (⟨Array.ofFn rates, Array.ofFn (fun i => some (now + exponentialClock (rates i) (u i)))⟩,
        ⟨[], []⟩) := by
  have hrl : ∀ a ∈ (Array.ofFn rates).toList, 0 ≤ a := by
    simp only [Array.toList_ofFn]
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (hr i).le
  unfold nrmInitialize
  rw [checkRates_real _ hrl]
  simp only [Bind.bind, Except.bind, realArithmetic, Bool.not_true, Bool.false_eq_true, ite_false,
    Array.toList_ofFn]
  have hinit := nrmInitializeAux_uniform rates u hr hu now []
  simp only [realArithmetic] at hinit
  rw [hinit]
  simp only [Except.bind, Pure.pure, Except.pure]
  congr 1
  simp [List.toArray_ofFn]

lemma nrmNext_vector_unique {n : Nat} (rates clocks : Fin n → ℝ) (i : Fin n)
    (hmin : ∀ j, j ≠ i → clocks i < clocks j) :
    nrmNext realArithmetic ⟨Array.ofFn rates, Array.ofFn (fun j => some (clocks j))⟩ =
      some ⟨clocks i, i.val⟩ := by
  unfold nrmNext
  rw [Array.toList_ofFn]
  rw [show List.ofFn (fun j => some (clocks j)) = (List.ofFn clocks).map some by simp only [List.map_ofFn, Function.comp_def]]
  have hi : i.val < (List.ofFn clocks).length := by simp
  have h : ∀ j : Nat, (hj : j < (List.ofFn clocks).length) → j ≠ i.val →
      (List.ofFn clocks)[i.val] < (List.ofFn clocks)[j] := by
    intro j hj hji
    simp only [List.getElem_ofFn]
    exact hmin ⟨j, by simpa using hj⟩ (by intro he; exact hji (congrArg Fin.val he))
  have he := nrmNextAux_unique (List.ofFn clocks) 0 i.val hi h
  simpa using he

lemma race_clocks_no_ties {n : Nat} (rates : Fin n → ℝ) (hr : ∀ i, 0 < rates i) :
    ∀ᵐ c : Fin n → ℝ ∂Measure.pi (fun i => expMeasure (rates i)),
      ∀ i j, i ≠ j → c i ≠ c j := by
  let (i : Fin n) : IsProbabilityMeasure (expMeasure (rates i)) := isProbabilityMeasure_expMeasure (hr i)
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun c h => (h hij).elim)
  · have hind := (iIndepFun_pi (μ := fun i => expMeasure (rates i)) (fun i : Fin n => (measurable_id : Measurable (id : ℝ → ℝ)).aemeasurable)).indepFun hij
    have hlaw := hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable
    simp only [Measure.pi_map_eval, measure_univ, Finset.prod_const_one, one_smul] at hlaw
    have hnull : ((expMeasure (rates i)).prod (expMeasure (rates j)))
        {p : ℝ × ℝ | p.1 = p.2} = 0 := by
      rw [Measure.prod_apply (by measurability)]
      have hsets (x : ℝ) : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by ext y; simp [eq_comm]
      have hsnull (x : ℝ) : expMeasure (rates j) {x} = 0 := by
        change (volume.withDensity (exponentialPDF (rates j))) ({x} : Set ℝ) = 0
        exact measure_singleton x
      simp_rw [hsets, hsnull]
      simp
    have hmap : (Measure.pi (fun i => expMeasure (rates i))) {c | c i = c j} = 0 := by
      change (Measure.pi (fun i => expMeasure (rates i))) ((fun c => (c i, c j)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0
      rw [← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) (by measurability), hlaw]
      exact hnull
    have hne : ∀ᵐ c : Fin n → ℝ ∂Measure.pi (fun i => expMeasure (rates i)), c i ≠ c j := by
      rw [ae_iff]; simpa only [not_not] using hmap
    exact hne.mono (fun c hc _ => hc)

/-- Probability of the concrete minimum selector, with no density assumed for its output. -/
theorem nrmNext_executable_joint_tail {n : Nat} (rates : Fin (n + 1) → ℝ)
    (hr : ∀ i, 0 < rates i) (i : Fin (n + 1)) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun j => expMeasure (rates j)))
      {c | ∃ e : Event ℝ,
        nrmNext realArithmetic ⟨Array.ofFn rates, Array.ofFn (fun j => some (c j))⟩ = some e ∧
          t < e.time ∧ e.reaction = i.val} =
      ENNReal.ofReal ((rates i / (∑ j, rates j)) * clockSurvival (∑ j, rates j) t) := by
  have hae : {c : Fin (n + 1) → ℝ | ∃ e : Event ℝ,
        nrmNext realArithmetic ⟨Array.ofFn rates, Array.ofFn (fun j => some (c j))⟩ = some e ∧
          t < e.time ∧ e.reaction = i.val} =ᵐ[Measure.pi (fun j => expMeasure (rates j))]
      raceRegion i t (fun _ => 0) := by
    filter_upwards [race_clocks_no_ties rates hr] with c hc
    apply propext
    constructor
    · rintro ⟨e, he, htime, hrx⟩
      unfold nrmNext at he
      rw [Array.toList_ofFn, show List.ofFn (fun j => some (c j)) = (List.ofFn c).map some by simp only [List.map_ofFn, Function.comp_def]] at he
      obtain ⟨j, hj, hrj, htj, hmin⟩ := nrmNextAux_sound _ 0 e he
      have hji : j = i.val := by omega
      have hci : e.time = c i := by simpa only [List.getElem_ofFn, hji, Fin.eta] using htj
      refine ⟨by simpa [hci] using htime, ?_⟩
      intro k
      have hki : i.succAbove k ≠ i := Fin.succAbove_ne i k
      have hle := hmin (c (i.succAbove k)) (List.mem_ofFn.mpr ⟨i.succAbove k, rfl⟩)
      simp only [hci] at hle
      simpa using lt_of_le_of_ne hle (hc i _ hki.symm)
    · rintro ⟨hci, hrest⟩
      have hmin : ∀ j, j ≠ i → c i < c j := by
        intro j hji
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        simpa using hrest k
      exact ⟨⟨c i, i.val⟩, nrmNext_vector_unique rates c i hmin, hci, rfl⟩
  rw [measure_congr hae, race_residual_probability rates hr i t ht (fun _ => 0) (fun _ => le_refl 0)]
  simp [clockSurvival]

lemma unitUniform_vector_ae_mem (n : Nat) :
    ∀ᵐ u : Fin n → ℝ ∂Measure.pi (fun _ => unitUniform), ∀ i, u i ∈ Ioo 0 1 := by
  rw [ae_all_iff]
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => unitUniform) (i := i)).eventually unitUniform_ae_mem

lemma nrmNext_event_iff_region {n : Nat} (rates c : Fin (n + 1) → ℝ)
    (hc : ∀ i j, i ≠ j → c i ≠ c j) (i : Fin (n + 1)) (t : ℝ) :
    (∃ e : Event ℝ,
      nrmNext realArithmetic ⟨Array.ofFn rates, Array.ofFn (fun j => some (c j))⟩ = some e ∧
        t < e.time ∧ e.reaction = i.val) ↔ c ∈ raceRegion i t (fun _ => 0) := by
  constructor
  · rintro ⟨e, he, htime, hrx⟩
    unfold nrmNext at he
    rw [Array.toList_ofFn, show List.ofFn (fun j => some (c j)) =
      (List.ofFn c).map some by simp only [List.map_ofFn, Function.comp_def]] at he
    obtain ⟨j, hj, hrj, htj, hmin⟩ := nrmNextAux_sound _ 0 e he
    have hji : j = i.val := by omega
    have hci : e.time = c i := by simpa only [List.getElem_ofFn, hji, Fin.eta] using htj
    refine ⟨by simpa [hci] using htime, ?_⟩
    intro k
    have hle := hmin (c (i.succAbove k)) (List.mem_ofFn.mpr ⟨i.succAbove k, rfl⟩)
    simp only [hci] at hle
    simpa using lt_of_le_of_ne hle (hc i _ (Fin.succAbove_ne i k).symm)
  · rintro ⟨hci, hrest⟩
    have hmin : ∀ j, j ≠ i → c i < c j := by
      intro j hji
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      simpa using hrest k
    exact ⟨⟨c i, i.val⟩, nrmNext_vector_unique rates c i hmin, hci, rfl⟩

/-- The complete NRM initialization and next-event computation, driven by IID uniforms. -/
theorem nrm_uniform_executable_joint_tail {n : Nat} (rates : Fin (n + 1) → ℝ)
    (hr : ∀ i, 0 < rates i) (i : Fin (n + 1)) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin (n + 1) => unitUniform))
      {u | ∃ (s : NRMState ℝ) (r : Tape ℝ) (e : Event ℝ),
        nrmInitialize realArithmetic (tapeSource ℝ) (Array.ofFn rates) 0
          ⟨[], List.ofFn (fun j => -log (u j))⟩ = .ok (s, r) ∧
        nrmNext realArithmetic s = some e ∧ t < e.time ∧ e.reaction = i.val} =
      ENNReal.ofReal ((rates i / (∑ j, rates j)) * clockSurvival (∑ j, rates j) t) := by
  let f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
    fun u j => exponentialClock (rates j) (u j)
  have hf : Measurable f := Measurable.of_eval (fun j =>
    (measurable_exponentialClock _).comp (measurable_pi_apply j))
  have hlaw := race_uniform_input_law rates hr
  have hnoties : ∀ᵐ u : Fin (n + 1) → ℝ ∂Measure.pi (fun _ => unitUniform),
      ∀ j k, j ≠ k → f u j ≠ f u k := by
    apply ae_of_ae_map (μ := Measure.pi (fun _ : Fin (n + 1) => unitUniform))
      (p := fun c => ∀ j k, j ≠ k → c j ≠ c k) hf.aemeasurable
    rw [hlaw]
    exact race_clocks_no_ties rates hr
  have hae : {u | ∃ (s : NRMState ℝ) (r : Tape ℝ) (e : Event ℝ),
        nrmInitialize realArithmetic (tapeSource ℝ) (Array.ofFn rates) 0
          ⟨[], List.ofFn (fun j => -log (u j))⟩ = .ok (s, r) ∧
        nrmNext realArithmetic s = some e ∧ t < e.time ∧ e.reaction = i.val} =ᵐ[
          Measure.pi (fun _ => unitUniform)] f ⁻¹' raceRegion i t (fun _ => 0) := by
    filter_upwards [unitUniform_vector_ae_mem (n + 1), hnoties] with u hu hc
    apply propext
    have hex := nrmInitialize_uniform_executes rates u hr hu 0
    simp only [zero_add] at hex
    simp only [mem_setOf_eq, hex, Except.ok.injEq, Prod.mk.injEq, mem_preimage]
    constructor
    · rintro ⟨s, r, e, ⟨hs, hrng⟩, he, htime, hi⟩
      subst s
      exact (nrmNext_event_iff_region rates (f u) hc i t).mp ⟨e, he, htime, hi⟩
    · intro h
      obtain ⟨e, he, htime, hi⟩ := (nrmNext_event_iff_region rates (f u) hc i t).mpr h
      exact ⟨_, _, e, ⟨rfl, rfl⟩, he, htime, hi⟩
  rw [measure_congr hae, ← Measure.map_apply hf (by unfold raceRegion; measurability), hlaw,
    race_residual_probability rates hr i t ht (fun _ => 0) (fun _ => le_refl 0)]
  simp [clockSurvival]

end JumpProcessesLean.Proofs
