import JumpProcessesLean.Proofs.OperationalNRM

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Real Set

noncomputable def nrmFresh (old new : ℝ) (j fired : Nat) : Bool :=
  decide (0 < new ∧ (j = fired ∨ ¬0 < old))

noncomputable def nrmUpdatedClock (old new clock u now : ℝ) (j fired : Nat) : Option ℝ :=
  if 0 < new then
    some (if j = fired ∨ ¬0 < old then now + exponentialClock new u
      else rescaleClock realArithmetic now old new clock)
  else none

noncomputable def nrmFreshExponentials {n : Nat} (old new u : Fin n → ℝ)
    (index fired : Nat) : List ℝ :=
  (List.ofFn (fun j => if nrmFresh (old j) (new j) (index + j.val) fired then
    some (-log (u j)) else none)).filterMap id

/-- Exact execution of the complete update, including disabled and reactivated channels.
The tape contains precisely the fresh draws that the implementation consumes. -/
theorem nrmUpdateAllAux_uniform {n : Nat} (old new c u : Fin n → ℝ)
    (hu : ∀ j, u j ∈ Ioo 0 1) (now : ℝ)
    (hc : ∀ j, 0 < old j → now ≤ c j) (index fired : Nat) (us es : List ℝ) :
    nrmUpdateAllAux realArithmetic (tapeSource ℝ) fired now
      (List.ofFn old) (List.ofFn (fun j => if 0 < old j then some (c j) else none))
      (List.ofFn new) index
      ⟨us, nrmFreshExponentials old new u index fired ++ es⟩ =
      .ok (List.ofFn (fun j => nrmUpdatedClock (old j) (new j) (c j) (u j)
        now (index + j.val) fired), ⟨us, es⟩) := by
  induction n generalizing index with
  | zero => simp [nrmUpdateAllAux, nrmFreshExponentials, List.ofFn_zero]
  | succ n ih =>
    have htape : nrmFreshExponentials old new u index fired =
        (if nrmFresh (old 0) (new 0) index fired then [-log (u 0)] else []) ++
        nrmFreshExponentials (fun j => old j.succ) (fun j => new j.succ)
          (fun j => u j.succ) (index + 1) fired := by
      unfold nrmFreshExponentials
      rw [List.ofFn_succ]
      cases h : nrmFresh (old 0) (new 0) index fired <;>
        simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hi := ih (fun j => old j.succ) (fun j => new j.succ)
      (fun j => c j.succ) (fun j => u j.succ) (fun j => hu j.succ)
      (fun j => hc j.succ) (index + 1)
    simp only [List.ofFn_succ, htape, List.append_assoc, nrmUpdateAllAux]
    by_cases hn : 0 < new 0
    · by_cases hf : index = fired ∨ ¬0 < old 0
      · have he : 0 < -log (u 0) := neg_pos.mpr (log_neg (hu 0).1 (hu 0).2)
        have ht : now < now + -log (u 0) / new 0 := lt_add_of_pos_right _ (div_pos he hn)
        have hcond : ¬(index ≠ fired ∧ 0 < old 0) := by tauto
        have hd : drawExponential realArithmetic (tapeSource ℝ)
            (⟨us, -log (u 0) :: (nrmFreshExponentials (fun j => old j.succ)
              (fun j => new j.succ) (fun j => u j.succ) (index + 1) fired ++ es)⟩ : Tape ℝ) =
          .ok (-log (u 0), ⟨us, nrmFreshExponentials (fun j => old j.succ)
            (fun j => new j.succ) (fun j => u j.succ) (index + 1) fired ++ es⟩) := by
          simp [drawExponential, tapeSource, realArithmetic, he, Bind.bind, Except.bind]
          rfl
        have hcondB : (index != fired && decide (0 < old 0)) = false := by
          rcases hf with h | h
          · simp [h]
          · simp [h]
        have hf' : index = fired ∨ old 0 ≤ 0 := by simpa only [not_lt] using hf
        simp only [realArithmetic] at hi hd
        simp [nrmFresh, hn, hf', hcondB, realArithmetic, hd, ht, hi,
          Bind.bind, Except.bind, Pure.pure, Except.pure, nrmUpdatedClock, exponentialClock,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · have ho : 0 < old 0 := by tauto
        have hnf : index ≠ fired := by tauto
        have hc0 := hc 0 ho
        have hp : 0 ≤ (old 0 / new 0) * (c 0 - now) :=
          mul_nonneg (div_pos ho hn).le (sub_nonneg.mpr hc0)
        have hres : now ≤ rescaleClock realArithmetic now (old 0) (new 0) (c 0) := by
          change now ≤ now + (old 0 / new 0) * (c 0 - now)
          linarith
        have hcondB : (index != fired && decide (0 < old 0)) = true := by simp [hnf, ho]
        simp only [realArithmetic] at hi hres
        simp [nrmFresh, hn, hnf, ho, hcondB, realArithmetic, hc0, hres, hi,
          Bind.bind, Except.bind, Pure.pure, Except.pure, nrmUpdatedClock,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · simp only [realArithmetic] at hi
      simp [nrmFresh, hn, realArithmetic, hi, Bind.bind, Except.bind, Pure.pure, Except.pure,
        nrmUpdatedClock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The public NRM update used by the simulation driver, with the complete graph.
Zero rates are admitted on both sides of the update. -/
theorem nrmUpdate_uniform_executes {n : Nat} (old new c u : Fin n → ℝ)
    (hn : ∀ j, 0 ≤ new j) (hu : ∀ j, u j ∈ Ioo 0 1)
    (now : ℝ) (hc : ∀ j, 0 < old j → now ≤ c j)
    (fired : Fin n) (us es : List ℝ) :
    nrmUpdate realArithmetic (tapeSource ℝ)
      ⟨Array.ofFn old, Array.ofFn (fun j => if 0 < old j then some (c j) else none)⟩
      (Array.ofFn new) fired.val now (List.range n).toArray
      ⟨us, nrmFreshExponentials old new u 0 fired.val ++ es⟩ =
      .ok (⟨Array.ofFn new, Array.ofFn (fun j =>
        nrmUpdatedClock (old j) (new j) (c j) (u j) now j.val fired.val)⟩, ⟨us, es⟩) := by
  have hnew : ∀ a ∈ (Array.ofFn new).toList, 0 ≤ a := by
    simp only [Array.toList_ofFn]
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact hn j
  unfold nrmUpdate
  simp only [Array.size_ofFn, bne_self_eq_false, Bool.false_or,
    show (fired.val >= n) = false from by simp [Nat.not_le.mpr fired.isLt], ite_false]
  rw [checkRates_real _ hnew]
  simp only [Bind.bind, Except.bind, realArithmetic, Bool.not_true,
    Bool.false_eq_true, ite_false, List.toList_toArray, ite_true, Array.toList_ofFn]
  have hex := nrmUpdateAllAux_uniform old new c u hu now hc 0 fired.val us es
  simp only [realArithmetic, Nat.zero_add] at hex
  rw [hex]
  simp [Except.bind, Pure.pure, Except.pure, List.toArray_ofFn]

/-- Observes the residual vector returned by the actual public NRM update. -/
noncomputable def nrmActualResidual {n : Nat} (old new : Fin n → ℝ)
    (i : Fin n) (c : Fin n → ℝ) (u : ℝ) : Fin n → ℝ :=
  match nrmUpdate realArithmetic (tapeSource ℝ)
    ⟨Array.ofFn old, Array.ofFn (fun j => if 0 < old j then some (c j) else none)⟩
    (Array.ofFn new) i.val (c i) (List.range n).toArray
    ⟨[], nrmFreshExponentials old new (fun _ => u) 0 i.val⟩ with
  | .ok (state, _) => fun j => (state.clocks[j.val]!).getD (c i) - c i
  | _ => fun _ => 0

lemma nrmActualResidual_executes {n : Nat} (old new : Fin n → ℝ)
    (ho : ∀ j, 0 < old j) (hn : ∀ j, 0 < new j) (i : Fin n)
    (c : Fin n → ℝ) (hmin : ∀ j, c i ≤ c j) (u : ℝ) (hu : u ∈ Ioo 0 1) :
    nrmActualResidual old new i c u = fun j =>
      if j = i then exponentialClock (new j) u else
        rescaleClock realArithmetic (c i) (old j) (new j) (c j) - c i := by
  have hex := nrmUpdate_uniform_executes old new c (fun _ => u) (fun j => (hn j).le)
    (fun _ => hu) (c i) (fun j _ => hmin j) i [] []
  simp only [List.append_nil] at hex
  unfold nrmActualResidual
  rw [hex]
  funext j
  have hget : (Array.ofFn (fun k => nrmUpdatedClock (old k) (new k) (c k) u (c i) k.val i.val))[j.val]! =
      nrmUpdatedClock (old j) (new j) (c j) u (c i) j.val i.val := by simp [j.isLt]
  dsimp only
  rw [hget]
  by_cases hji : j = i
  · subst j
    simp [nrmUpdatedClock, hn i]
  · have hval : j.val ≠ i.val := by exact fun h => hji (Fin.ext h)
    simp [nrmUpdatedClock, hn j, ho j, hval, hji]

/-- The complete operational positive-rate NRM cache invariant: at a winning event,
the public update's entire residual vector has fresh independent exponential tails. -/
theorem nrm_operational_update_invariant {n : Nat} (old new : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 < old j) (hn : ∀ j, 0 < new j) (i : Fin (n + 1))
    (t : ℝ) (ht : 0 ≤ t) (s : Fin (n + 1) → ℝ) (hs : ∀ j, 0 ≤ s j) :
    ((Measure.pi (fun j => expMeasure (old j))).prod unitUniform)
      {p | t < p.1 i ∧ (∀ j, j ≠ i → p.1 i < p.1 j) ∧
        ∀ j, s j < nrmActualResidual old new i p.1 p.2 j} =
      ENNReal.ofReal ((old i / (∑ j, old j)) * clockSurvival (∑ j, old j) t) *
        ∏ j, ENNReal.ofReal (clockSurvival (new j) (s j)) := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (old j)) := isProbabilityMeasure_expMeasure (ho j)
  have hu : ∀ᵐ p : (Fin (n + 1) → ℝ) × ℝ
      ∂(Measure.pi (fun j => expMeasure (old j))).prod unitUniform, p.2 ∈ Ioo 0 1 :=
    (measurePreserving_snd (μ := Measure.pi (fun j => expMeasure (old j)))
      (ν := unitUniform)).quasiMeasurePreserving.tendsto_ae.eventually unitUniform_ae_mem
  have heq : {p : (Fin (n + 1) → ℝ) × ℝ |
      t < p.1 i ∧ (∀ j, j ≠ i → p.1 i < p.1 j) ∧
        ∀ j, s j < nrmActualResidual old new i p.1 p.2 j} =ᵐ[
        (Measure.pi (fun j => expMeasure (old j))).prod unitUniform]
      {p | t < p.1 i ∧ exponentialClock (new i) p.2 > s i ∧
        ∀ j : Fin n, s (i.succAbove j) <
          rescaleClock realArithmetic (p.1 i) (old (i.succAbove j))
            (new (i.succAbove j)) (p.1 (i.succAbove j)) - p.1 i} := by
    filter_upwards [hu] with p hup
    apply propext
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor
    · rintro ⟨htp, hmin, hres⟩
      have hex := nrmActualResidual_executes old new ho hn i p.1
        (fun j => if h : j = i then by simp [h] else (hmin j h).le) p.2 hup
      rw [hex] at hres
      refine ⟨htp, by simpa using hres i, ?_⟩
      intro j
      simpa [Fin.succAbove_ne i j] using hres (i.succAbove j)
    · rintro ⟨htp, hfresh, hrest⟩
      have hmin : ∀ j, j ≠ i → p.1 i < p.1 j := by
        intro j hji
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        have hpos : 0 < rescaleClock realArithmetic (p.1 i) (old (i.succAbove k))
            (new (i.succAbove k)) (p.1 (i.succAbove k)) - p.1 i := (hs _).trans_lt (hrest k)
        change 0 < p.1 i + (old _ / new _) * (p.1 (i.succAbove k) - p.1 i) - p.1 i at hpos
        have hp := div_pos (ho (i.succAbove k)) (hn (i.succAbove k))
        nlinarith
      have hex := nrmActualResidual_executes old new ho hn i p.1
        (fun j => if h : j = i then by simp [h] else (hmin j h).le) p.2 hup
      refine ⟨htp, hmin, ?_⟩
      rw [hex]
      intro j
      by_cases hji : j = i
      · subst j; simpa using hfresh
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        simpa [Fin.succAbove_ne i k] using hrest k
  rw [measure_congr heq]
  exact nrm_fresh_and_survivor_invariant old new ho hn i t ht s hs

end JumpProcessesLean.Proofs
