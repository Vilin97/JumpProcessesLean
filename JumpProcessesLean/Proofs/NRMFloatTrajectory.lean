import JumpProcessesLean.Proofs.RSSAFloatTrajectory

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- Numerical update conditions with no propagated error hypotheses. The previous
errors are proved by trajectory induction before constructing a certificate. -/
structure NRMUpdateConditions {n : Nat} (old new c e : Fin n → Binary64)
    (er : Fin n → ℝ) (now : Binary64) (εc εn δ : ℝ) (fired : Fin n) : Prop where
  oldFinite : ∀ j, ExecFloat.Binary.isFinite (old j) = true
  newValid : ∀ j, validRate binary64Arithmetic (new j) = true
  cacheFinite : ∀ j, ExecFloat.Binary.isFinite (c j) = true
  nowFinite : ExecFloat.Binary.isFinite now = true
  flags : ∀ j, UpdateFlags binary64Arithmetic (old j) (new j) (c j) (e j) now j.val fired.val
  newNonzero : ∀ j, 0 < floatReal (new j) → Model.isZero (ExecFloat.Binary.toModel (new j)) = false
  freshFinite : ∀ j, ExecFloat.Binary.isFinite (e j) = true
  freshQuotient : ∀ j, 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite (e j / new j) = true
  freshClock : ∀ j, 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite (now + e j / new j) = true
  freshBudget : ∀ j, 0 < floatReal (new j) →
    floatEpsilon (floatReal now + floatReal (e j / new j)) +
      floatEpsilon (floatReal (e j) / floatReal (new j)) +
      εn + |floatReal (e j) - er j| / floatReal (new j) ≤ δ
  rescaleQuotient : ∀ j, j ≠ fired → 0 < floatReal (old j) → 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite (old j / new j) = true
  rescaleDifference : ∀ j, j ≠ fired → 0 < floatReal (old j) → 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite (c j - now) = true
  rescaleProduct : ∀ j, j ≠ fired → 0 < floatReal (old j) → 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite ((old j / new j) * (c j - now)) = true
  rescaleFinite : ∀ j, j ≠ fired → 0 < floatReal (old j) → 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite (rescaleClock binary64Arithmetic now (old j) (new j) (c j)) = true
  rescaleBudget : ∀ j, j ≠ fired → 0 < floatReal (old j) → 0 < floatReal (new j) →
    rescaleRoundBudget now (old j) (new j) (c j) +
      |floatReal (old j) / floatReal (new j)| * εc +
      |1 - floatReal (old j) / floatReal (new j)| * εn ≤ δ


def NRMUpdateConditions.toCertificate {n : Nat} (old new c e : Fin n → Binary64)
    (cr er : Fin n → ℝ) (now : Binary64) (nr εc εn δ : ℝ) (fired : Fin n)
    (h : NRMUpdateConditions old new c e er now εc εn δ fired)
    (hnow : |floatReal now - nr| ≤ εn)
    (hcache : ∀ j, 0 < floatReal (old j) → |floatReal (c j) - cr j| ≤ εc) :
    NRMUpdateCertificate old new c e cr er now nr εc εn δ fired where
  oldFinite := h.oldFinite
  newValid := h.newValid
  cacheFinite := h.cacheFinite
  nowFinite := h.nowFinite
  flags := h.flags
  newNonzero := h.newNonzero
  freshFinite := h.freshFinite
  freshQuotient := h.freshQuotient
  freshClock := h.freshClock
  freshBudget := h.freshBudget
  rescaleQuotient := h.rescaleQuotient
  rescaleDifference := h.rescaleDifference
  rescaleProduct := h.rescaleProduct
  rescaleFinite := h.rescaleFinite
  rescaleBudget := h.rescaleBudget
  nowError := hnow
  cacheError := hcache

noncomputable def nrmFloatClocks {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64) : Nat → Fin (n + 1) → Binary64
  | 0 => fun j => start + e 0 j / rates 0 j
  | k + 1 => fun j =>
    let c := nrmFloatClocks rates e marks start k
    let now := c (marks k)
    if j = marks k then now + e (k + 1) j / rates (k + 1) j
    else rescaleClock binary64Arithmetic now (rates k j) (rates (k + 1) j) (c j)

noncomputable def nrmRealClocks {n : Nat} (rates : Nat → Fin (n + 1) → Binary64)
    (er : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1)) (start : ℝ) : Nat → Fin (n + 1) → ℝ
  | 0 => fun j => start + er 0 j / floatReal (rates 0 j)
  | k + 1 => fun j =>
    let c := nrmRealClocks rates er marks start k
    let now := c (marks k)
    if j = marks k then now + er (k + 1) j / floatReal (rates (k + 1) j)
    else now + (floatReal (rates k j) / floatReal (rates (k + 1) j)) * (c j - now)

noncomputable def nrmFloatTimes {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64) : Nat → Binary64
  | 0 => start
  | k + 1 => nrmFloatClocks rates e marks start k (marks k)

noncomputable def nrmRealTimes {n : Nat} (rates : Nat → Fin (n + 1) → Binary64)
    (er : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1)) (start : ℝ) : Nat → ℝ
  | 0 => start
  | k + 1 => nrmRealClocks rates er marks start k (marks k)

noncomputable def nrmFloatCache {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64) (k : Nat) : NRMState Binary64 :=
  ⟨Array.ofFn (rates k), Array.ofFn (fun j => some (nrmFloatClocks rates e marks start k j))⟩

noncomputable def nrmFloatTape {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) : Nat → Nat → List Binary64
  | _, 0 => []
  | k, count + 1 =>
    updateTape binary64Arithmetic (rates k) (rates (k + 1)) (e (k + 1)) 0 (marks k).val ++
      nrmFloatTape rates e marks (k + 1) count

structure NRMInitConditions {n : Nat} (rates e : Fin (n + 1) → Binary64)
    (er : Fin (n + 1) → ℝ) (start : Binary64) (sr η : ℝ) : Prop where
  rateValid : ∀ j, validRate binary64Arithmetic (rates j) = true
  ratePositive : ∀ j, binary64Arithmetic.lt 0 (rates j) = true
  rateNonzero : ∀ j, Model.isZero (ExecFloat.Binary.toModel (rates j)) = false
  startFinite : ExecFloat.Binary.isFinite start = true
  exponentialValid : ∀ j, exponentialFlag (e j) = true
  quotientFinite : ∀ j, ExecFloat.Binary.isFinite (e j / rates j) = true
  clockValid : ∀ j, clockFlag start (e j) (rates j) = true
  budget : ∀ j,
    floatEpsilon (floatReal start + floatReal (e j / rates j)) +
    floatEpsilon (floatReal (e j) / floatReal (rates j)) +
    |floatReal start - sr| + |floatReal (e j) - er j| / floatReal (rates j) ≤ η

lemma finite_of_valid (a : Binary64) (h : validRate binary64Arithmetic a = true) :
    ExecFloat.Binary.isFinite a = true := by
  rw [validRate, Bool.and_eq_true] at h
  exact h.1

lemma real_positive_of_flag (a : Binary64) (hf : ExecFloat.Binary.isFinite a = true)
    (hp : binary64Arithmetic.lt 0 a = true) : 0 < floatReal a := by
  simpa only [floatReal_zero] using (float_lt_real 0 a float_zero_finite hf).mp (of_decide_eq_true hp)

/-- Actual FloatLib initialization at an arbitrary start and on any suffix tape. -/
theorem nrm_float_initialize_conditions {n : Nat} (rates e : Fin (n + 1) → Binary64)
    (er : Fin (n + 1) → ℝ) (start : Binary64) (sr η : ℝ)
    (hc : NRMInitConditions rates e er start sr η) (us es : List Binary64) :
    nrmInitialize binary64Arithmetic (tapeSource Binary64) (Array.ofFn rates) start
      ⟨us, List.ofFn e ++ es⟩ =
      .ok (⟨Array.ofFn rates, Array.ofFn (fun j => some (start + e j / rates j))⟩, ⟨us, es⟩) ∧
    ∀ j, |floatReal (start + e j / rates j) - (sr + er j / floatReal (rates j))| ≤ η := by
  constructor
  · unfold nrmInitialize
    rw [show checkRates binary64Arithmetic (Array.ofFn rates) = .ok () from
      checkRatesAux_valid _ _ (by
        intro a ha
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (by simpa only [Array.toList_ofFn] using ha)
        exact hc.rateValid j) 0]
    simp only [Bind.bind, Except.bind, show binary64Arithmetic.finite start = true from hc.startFinite,
      Bool.not_true, Bool.false_eq_true, ite_false, Array.toList_ofFn]
    rw [nrmInitializeAux_flags binary64Arithmetic rates e start hc.ratePositive hc.exponentialValid hc.clockValid us es]
    simp only [Except.bind, Pure.pure, Except.pure, List.toArray_ofFn]
    rfl
  · intro j
    have hf := finite_of_valid (rates j) (hc.rateValid j)
    have he : ExecFloat.Binary.isFinite (e j) = true := by
      have h := hc.exponentialValid j
      rw [exponentialFlag, Bool.and_eq_true] at h
      exact h.1
    have ht : ExecFloat.Binary.isFinite (start + e j / rates j) = true := by
      have h := hc.clockValid j
      rw [clockFlag, Bool.and_eq_true] at h
      exact h.1
    have hclock := float_clock_time_error start (e j) (rates j) hc.startFinite he hf
      (hc.rateNonzero j) (hc.quotientFinite j) ht
    have hsource : |(floatReal start + floatReal (e j) / floatReal (rates j)) -
        (sr + er j / floatReal (rates j))| ≤
        |floatReal start - sr| + |floatReal (e j) - er j| / floatReal (rates j) := by
      have hx : (floatReal start + floatReal (e j) / floatReal (rates j)) -
        (sr + er j / floatReal (rates j)) =
        (floatReal start - sr) + (floatReal (e j) - er j) / floatReal (rates j) := by ring
      rw [hx]
      exact (abs_add_le _ _).trans (by rw [abs_div, abs_of_pos (real_positive_of_flag _ hf (hc.ratePositive j))])
    exact ((abs_sub_le _ _ _).trans (add_le_add hclock hsource)).trans
      (by simpa only [add_assoc] using hc.budget j)

lemma update_clock_positive_schedule {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64) (k : Nat)
    (hp : ∀ l j, binary64Arithmetic.lt 0 (rates l j) = true) (j : Fin (n + 1)) :
    updateClock binary64Arithmetic (rates k j) (rates (k + 1) j)
      (nrmFloatClocks rates e marks start k j) (e (k + 1) j)
      (nrmFloatTimes rates e marks start (k + 1)) j.val (marks k).val =
      some (nrmFloatClocks rates e marks start (k + 1) j) := by
  by_cases hj : j = marks k
  · subst j
    simp only [updateClock, hp, show binary64Arithmetic.zero = (0 : Binary64) from rfl,
      ite_true, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false,
      nrmFloatTimes, nrmFloatClocks]
    simp
    rfl
  · have hv : j.val ≠ (marks k).val := fun h => hj (Fin.ext h)
    have hb : (j.val != (marks k).val) = true := by simp [hv]
    simp only [updateClock, hp, show binary64Arithmetic.zero = (0 : Binary64) from rfl,
      ite_true, hb, Bool.true_and,
      nrmFloatTimes, nrmFloatClocks, hj, ite_false]

/-- Every cache error is derived from the initialization and prior errors. The
numerical update conditions never assume a cache-error bound. -/
theorem nrm_float_cache_errors {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (er : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (start : Binary64) (sr : ℝ) (η : Nat → ℝ) (limit : Nat)
    (hp : ∀ l j, binary64Arithmetic.lt 0 (rates l j) = true)
    (hv : ∀ l j, validRate binary64Arithmetic (rates l j) = true)
    (hi : NRMInitConditions (rates 0) (e 0) (er 0) start sr (η 0))
    (hc : ∀ k, k < limit → NRMUpdateConditions (rates k) (rates (k + 1))
      (nrmFloatClocks rates e marks start k) (e (k + 1)) (er (k + 1))
      (nrmFloatTimes rates e marks start (k + 1)) (η k) (η k) (η (k + 1)) (marks k))
    (k : Nat) (hk : k ≤ limit) :
    ∀ j, |floatReal (nrmFloatClocks rates e marks start k j) - nrmRealClocks rates er marks sr k j| ≤ η k := by
  induction k with
  | zero => exact (nrm_float_initialize_conditions _ _ _ _ _ _ hi [] []).2
  | succ k ih =>
    intro j
    have hnow : |floatReal (nrmFloatTimes rates e marks start (k + 1)) -
        nrmRealTimes rates er marks sr (k + 1)| ≤ η k := ih (by omega) (marks k)
    have cert := (hc k (by omega)).toCertificate _ _ _ _ (nrmRealClocks rates er marks sr k)
      (er (k + 1)) _ (nrmRealTimes rates er marks sr (k + 1)) _ _ _ _ hnow
      (fun j _ => ih (by omega) j)
    have h := (nrm_float_update_certificate_refines _ _ _ _ _ _ _ _ _ _ _ _ cert j).2
      (nrmFloatClocks rates e marks start (k + 1) j) (update_clock_positive_schedule _ _ _ _ k hp j)
    have he : updatedRealClock (rates k) (rates (k + 1)) (nrmRealClocks rates er marks sr k)
      (er (k + 1)) (nrmRealTimes rates er marks sr (k + 1)) (marks k) j =
        nrmRealClocks rates er marks sr (k + 1) j := by
      have hpos := real_positive_of_flag (rates k j) (finite_of_valid _ (hv k j)) (hp k j)
      by_cases hj : j = marks k <;> simp [updatedRealClock, nrmRealTimes, nrmRealClocks, hj, hpos]
    simpa only [he] using h

/-- The full graph update returns exactly the recursively computed float cache. -/
theorem nrm_float_update_schedule {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64) (k : Nat)
    (hp : ∀ l j, binary64Arithmetic.lt 0 (rates l j) = true)
    (hv : ∀ l j, validRate binary64Arithmetic (rates l j) = true)
    (hnow : ExecFloat.Binary.isFinite (nrmFloatTimes rates e marks start (k + 1)) = true)
    (hc : ∀ j, UpdateFlags binary64Arithmetic (rates k j) (rates (k + 1) j)
      (nrmFloatClocks rates e marks start k j) (e (k + 1) j)
      (nrmFloatTimes rates e marks start (k + 1)) j.val (marks k).val)
    (us es : List Binary64) :
    nrmUpdate binary64Arithmetic (tapeSource Binary64) (nrmFloatCache rates e marks start k)
      (Array.ofFn (rates (k + 1))) (marks k).val (nrmFloatTimes rates e marks start (k + 1))
      (List.range (n + 1)).toArray
      ⟨us, updateTape binary64Arithmetic (rates k) (rates (k + 1)) (e (k + 1)) 0 (marks k).val ++ es⟩ =
      .ok (nrmFloatCache rates e marks start (k + 1), ⟨us, es⟩) := by
  have hex := nrm_float_update_executes (rates k) (rates (k + 1))
    (nrmFloatClocks rates e marks start k) (e (k + 1))
    (nrmFloatTimes rates e marks start (k + 1)) (marks k) (hv (k + 1)) hnow hc us es
  have hcl : (fun j => updateClock binary64Arithmetic (rates k j) (rates (k + 1) j)
      (nrmFloatClocks rates e marks start k j) (e (k + 1) j)
      (nrmFloatTimes rates e marks start (k + 1)) j.val (marks k).val) =
      fun j => some (nrmFloatClocks rates e marks start (k + 1) j) :=
    funext (fun j => update_clock_positive_schedule rates e marks start k hp j)
  rw [hcl] at hex
  simpa only [hp, ite_true, nrmFloatCache] using hex

/-- Complete FloatLib NRM trajectory approximation for positive-rate numerical
certificates. Initialization and every persistent cache error are proved;
reaction preservation follows from the exact race gaps. -/
theorem nrm_float_trajectory_close {σ : Type} {n : Nat} (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Fin (n + 1))
    (rates e : Nat → Fin (n + 1) → Binary64) (er : Nat → Fin (n + 1) → ℝ)
    (hm : ∀ k, mf.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, mf.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ) (fuel cap : Nat) (save : Bool)
    (hp : ∀ l j, binary64Arithmetic.lt 0 (rates l j) = true)
    (hv : ∀ l j, validRate binary64Arithmetic (rates l j) = true)
    (hi : NRMInitConditions (rates 0) (e 0) (er 0) start sr (η 0))
    (hc : ∀ k, k < fuel → NRMUpdateConditions (rates k) (rates (k + 1))
      (nrmFloatClocks rates e marks start k) (e (k + 1)) (er (k + 1))
      (nrmFloatTimes rates e marks start (k + 1)) (η k) (η k) (η (k + 1)) (marks k))
    (hcacheFinite : ∀ k, k ≤ fuel → ∀ j, ExecFloat.Binary.isFinite (nrmFloatClocks rates e marks start k j) = true)
    (hgap : ∀ k, k ≤ fuel → ∀ j, j ≠ marks k →
      nrmRealClocks rates er marks sr k (marks k) + 2 * η k < nrmRealClocks rates er marks sr k j)
    (hinc : ∀ k, k ≤ fuel → binary64Arithmetic.le (nrmFloatTimes rates e marks start k)
      (nrmFloatTimes rates e marks start (k + 1)) = true)
    (hrinc : ∀ k, k ≤ fuel → nrmRealTimes rates er marks sr k ≤ nrmRealTimes rates er marks sr (k + 1))
    (hbudget : ∀ k, k ≤ fuel → η k ≤ δ)
    (hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true) (hstart : binary64Arithmetic.lt start hf = true)
    (hhf : ExecFloat.Binary.isFinite hf = true) (hh : |floatReal hf - hr| ≤ δ)
    (h0 : |floatReal start - sr| ≤ δ)
    (hmargin : ∀ k, k ≤ fuel → 2 * δ < |nrmRealTimes rates er marks sr (k + 1) - hr|) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .nrm (states 0) start hf
        ⟨[], List.ofFn (e 0) ++ nrmFloatTape rates e marks 0 fuel⟩ fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (nrmRealTimes rates er marks sr) (fun k => (marks k).val) 0 (fuel + 1))) := by
  let tf := nrmFloatTimes rates e marks start
  let tr := nrmRealTimes rates er marks sr
  let tape := fun k count => (⟨[], nrmFloatTape rates e marks k (count - 1)⟩ : Tape Binary64)
  let cache := fun k => some (nrmFloatCache rates e marks start k)
  have herr := nrm_float_cache_errors rates e er marks start sr η fuel hp hv hi hc
  have hnext k hk := nrm_float_winner_approx (rates k) (nrmFloatClocks rates e marks start k)
    (nrmRealClocks rates er marks sr k) (marks k) (η k) (hcacheFinite k hk) (herr k hk) (hgap k hk)
  apply simulate_float_schedule_close (tapeSource Binary64) mf mr .nrm htransition states tf tr
    (fun k => (marks k).val) hf hr δ fuel cap save tape (fun k count => tape k (count + 1)) cache
    (⟨[], List.ofFn (e 0) ++ nrmFloatTape rates e marks 0 fuel⟩ : Tape Binary64)
  · dsimp only [initializeCache]
    dsimp only [tf, nrmFloatTimes]
    rw [hm 0, (nrm_float_initialize_conditions _ _ _ _ _ _ hi [] (nrmFloatTape rates e marks 0 fuel)).1]
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, tape, cache, tf,
      nrmFloatTimes, nrmFloatCache, nrmFloatClocks, Nat.add_sub_cancel]
  · exact hvalid
  · exact hstart
  · exact hhf
  · exact hh
  · exact h0
  · intro k count hk
    dsimp only [sampleEvent, cache, nrmFloatCache]
    rw [(hnext k (by omega)).1]
    rfl
  · exact hs
  · intro k count hk
    dsimp only [refreshCache, cache]
    rw [hm (k + 1)]
    simp only [Array.size_ofFn]
    have hh := nrm_float_update_schedule rates e marks start k hp hv (hcacheFinite k (by omega) (marks k))
      (hc k (by omega)).flags [] (nrmFloatTape rates e marks (k + 1) count)
    change (do
      let result ← nrmUpdate binary64Arithmetic (tapeSource Binary64) (nrmFloatCache rates e marks start k)
        (Array.ofFn (rates (k + 1))) (marks k).val (tf (k + 1)) (List.range (n + 1)).toArray
        ⟨[], nrmFloatTape rates e marks k (count + 1)⟩
      pure (some result.1, result.2)) = _
    rw [nrmFloatTape, hh]
    rfl
  · intro k hk
    exact hcacheFinite k hk (marks k)
  · exact hinc
  · exact hrinc
  · intro k hk
    exact (herr k hk (marks k)).trans (hbudget k hk)
  · exact hmargin

end JumpProcessesLean.Proofs
