import JumpProcessesLean.Proofs.FloatStopCertificates

/-!
# FloatLib NRM trajectories with inactive channels

The persistent FloatLib NRM cache stores `none` for inactive channels, draws fresh
clocks for fired and reactivated channels, rescales retained clocks and disables
channels whose new rate is zero. This file proves the trajectory refinement for this
masked cache, including absorbing states where every clock is inactive.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma float_lt_zero_decide (x : Binary64) (hx : ExecFloat.Binary.isFinite x = true) :
    binary64Arithmetic.lt 0 x = decide (0 < floatReal x) := by
  change decide ((0 : Binary64) < x) = decide (0 < floatReal x)
  have h := float_lt_real 0 x float_zero_finite hx
  rw [floatReal_zero] at h
  exact decide_eq_decide.mpr h

lemma nrmNextAux_opt_time_mem {α : Type} (op : Arithmetic α) (clocks : List (Option α)) (k : Nat)
    (e : Event α) (he : nrmNextAux op clocks k = some e) : some e.time ∈ clocks := by
  induction clocks generalizing k e with
  | nil => simp [nrmNextAux] at he
  | cons a rest ih =>
    cases a with
    | none =>
      simp only [nrmNextAux] at he
      exact List.mem_cons_of_mem _ (ih _ _ he)
    | some a =>
      simp only [nrmNextAux] at he
      cases h : nrmNextAux op rest (k + 1) with
      | none => simp only [h] at he; cases he; simp
      | some b =>
        simp only [h] at he
        split at he
        · cases he; simp
        · cases he; exact List.mem_cons_of_mem _ (ih _ _ h)

/-- IEEE comparisons on finite optional clocks refine real comparisons on decoded clocks. -/
theorem nrmNextAux_float_decode_opt (clocks : List (Option Binary64))
    (hf : ∀ c, some c ∈ clocks → ExecFloat.Binary.isFinite c = true) (k : Nat) :
    (nrmNextAux binary64Arithmetic clocks k).map
      (fun e => (⟨floatReal e.time, e.reaction⟩ : Event ℝ)) =
    nrmNextAux realArithmetic (clocks.map (Option.map floatReal)) k := by
  induction clocks generalizing k with
  | nil => rfl
  | cons a rest ih =>
    have hr := ih (fun c hc => hf c (by simp [hc])) (k + 1)
    cases a with
    | none =>
      simp only [List.map_cons, Option.map_none, nrmNextAux]
      exact hr
    | some a =>
      have ha := hf a (by simp)
      cases h : nrmNextAux binary64Arithmetic rest (k + 1) with
      | none =>
        simp only [h, Option.map_none] at hr
        simp only [List.map_cons, Option.map_some, nrmNextAux, h, ← hr, Option.map_some]
      | some b =>
        have hb := hf b.time (List.mem_cons_of_mem _ (nrmNextAux_opt_time_mem _ _ _ _ h))
        have hle := float_le_real a b.time ha hb
        have hcomp : binary64Arithmetic.le a b.time = realArithmetic.le (floatReal a) (floatReal b.time) := by
          simp only [binary64Arithmetic, realArithmetic]
          exact decide_eq_decide.mpr hle
        simp only [h, Option.map_some] at hr
        simp only [List.map_cons, Option.map_some, nrmNextAux, h, ← hr, hcomp]
        split <;> rfl

/-- The FloatLib selector on a masked cache chooses the certified active winner. -/
theorem nrm_float_winner_masked {n : Nat} (rates cf : Fin (n + 1) → Binary64)
    (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (η : ℝ)
    (hrf : ∀ j, ExecFloat.Binary.isFinite (rates j) = true)
    (hact : 0 < floatReal (rates i))
    (hf : ∀ j, ExecFloat.Binary.isFinite (cf j) = true)
    (herr : ∀ j, 0 < floatReal (rates j) → |floatReal (cf j) - c j| ≤ η)
    (hgap : ∀ j, j ≠ i → 0 < floatReal (rates j) → c i + 2 * η < c j) :
    nrmNext binary64Arithmetic ⟨Array.ofFn rates,
      Array.ofFn (fun j => if binary64Arithmetic.lt 0 (rates j) then some (cf j) else none)⟩ =
      some ⟨cf i, i.val⟩ ∧ |floatReal (cf i) - c i| ≤ η := by
  have hmin : ∀ j, j ≠ i → 0 < floatReal (rates j) → floatReal (cf i) < floatReal (cf j) := by
    intro j hj hjp
    have hi := abs_le.mp (herr i hact)
    have hj' := abs_le.mp (herr j hjp)
    linarith [hgap j hj hjp]
  have hreal := nrmNext_masked_unique (fun j => floatReal (rates j)) (fun j => floatReal (cf j)) i hact hmin
  have hlist : (List.ofFn (fun j => if binary64Arithmetic.lt 0 (rates j) then some (cf j) else none)).map
      (Option.map floatReal) =
      List.ofFn (fun j => if 0 < floatReal (rates j) then some (floatReal (cf j)) else none) := by
    rw [List.map_ofFn]
    congr 1
    funext j
    simp only [Function.comp_apply, float_lt_zero_decide _ (hrf j)]
    by_cases h : 0 < floatReal (rates j) <;> simp [h]
  have hd := nrmNextAux_float_decode_opt
    (List.ofFn (fun j => if binary64Arithmetic.lt 0 (rates j) then some (cf j) else none)) (by
      intro a ha
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp ha
      by_cases h : binary64Arithmetic.lt 0 (rates j) = true
      · simp only [h, ite_true, Option.some.injEq] at hj
        rw [← hj]
        exact hf j
      · simp [h] at hj) 0
  rw [hlist] at hd
  simp only [nrmNext, Array.toList_ofFn] at hreal hd ⊢
  rw [hreal] at hd
  constructor
  · cases h : nrmNextAux binary64Arithmetic
        (List.ofFn (fun j => if binary64Arithmetic.lt 0 (rates j) then some (cf j) else none)) 0 with
    | none => simp only [h, Option.map_none, reduceCtorEq] at hd
    | some e =>
      simp only [h, Option.map_some, Option.some.injEq] at hd
      have hrx : e.reaction = i.val := congrArg Event.reaction hd
      have htime := nrmNextAux_opt_time_mem binary64Arithmetic _ 0 e h
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp htime
      have hjact : binary64Arithmetic.lt 0 (rates j) = true := by
        by_contra hn
        simp [hn] at hj
      simp only [hjact, ite_true, Option.some.injEq] at hj
      have hjtime : floatReal (cf j) = floatReal (cf i) := by
        rw [hj]
        exact congrArg Event.time hd
      have hji : j = i := by
        by_contra hji
        have hjp : 0 < floatReal (rates j) := by
          rw [float_lt_zero_decide _ (hrf j)] at hjact
          exact of_decide_eq_true hjact
        exact (ne_of_lt (hmin j hji hjp)) hjtime.symm
      subst hji
      have heq : e = ⟨cf j, j.val⟩ := by
        cases e
        simp_all
      rw [heq]
  · exact herr i hact

lemma nrmNextAux_all_none {α : Type} (op : Arithmetic α) :
    ∀ (l : List (Option α)) (k : Nat), (∀ x ∈ l, x = none) → nrmNextAux op l k = none
  | [], _, _ => rfl
  | a :: rest, k, h => by
    have ha : a = none := h a (by simp)
    subst ha
    simp only [nrmNextAux]
    exact nrmNextAux_all_none op rest (k + 1) (fun x hx => h x (by simp [hx]))

/-- A masked cache with no active channel reports an absorbing state. -/
lemma nrm_float_absorbing_cache {n : Nat} (rates cf : Fin n → Binary64)
    (hz : ∀ j, binary64Arithmetic.lt 0 (rates j) = false) :
    nrmNext binary64Arithmetic ⟨Array.ofFn rates,
      Array.ofFn (fun j => if binary64Arithmetic.lt 0 (rates j) then some (cf j) else none)⟩ = none := by
  simp only [nrmNext, Array.toList_ofFn]
  apply nrmNextAux_all_none
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  simp [hz j]

/-- Exponentials consumed by a masked FloatLib initialization: active channels only. -/
def nrmFloatInitTape {n : Nat} (rates e : Fin n → Binary64) : List Binary64 :=
  (List.ofFn (fun j => if binary64Arithmetic.lt 0 (rates j) then some (e j) else none)).filterMap id

lemma nrmFloatInitTape_succ {n : Nat} (rates e : Fin (n + 1) → Binary64) :
    nrmFloatInitTape rates e = (if binary64Arithmetic.lt 0 (rates 0) then [e 0] else []) ++
      nrmFloatInitTape (fun j => rates j.succ) (fun j => e j.succ) := by
  unfold nrmFloatInitTape
  rw [List.ofFn_succ]
  cases h : binary64Arithmetic.lt 0 (rates 0) <;> simp [h]

/-- Native masked FloatLib initialization on any suffix tape. -/
theorem nrmInitializeAux_float_masked {n : Nat} (rates e : Fin n → Binary64) (now : Binary64)
    (he : ∀ j, binary64Arithmetic.lt 0 (rates j) = true → exponentialFlag (e j) = true)
    (ht : ∀ j, binary64Arithmetic.lt 0 (rates j) = true → clockFlag now (e j) (rates j) = true)
    (us es : List Binary64) :
    nrmInitializeAux binary64Arithmetic (tapeSource Binary64) now (List.ofFn rates)
      ⟨us, nrmFloatInitTape rates e ++ es⟩ =
      .ok (List.ofFn (fun j => if binary64Arithmetic.lt 0 (rates j) then some (now + e j / rates j)
        else none), ⟨us, es⟩) := by
  induction n with
  | zero => simp [List.ofFn_zero, nrmInitializeAux, nrmFloatInitTape]
  | succ n ih =>
    have hi := ih (fun j => rates j.succ) (fun j => e j.succ) (fun j h => he j.succ h)
      (fun j h => ht j.succ h)
    rw [nrmFloatInitTape_succ]
    by_cases h0 : binary64Arithmetic.lt 0 (rates 0) = true
    · have he0 : (binary64Arithmetic.finite (e 0) && binary64Arithmetic.lt binary64Arithmetic.zero (e 0)) =
          true := he 0 h0
      have ht0 : (binary64Arithmetic.finite (binary64Arithmetic.add now (binary64Arithmetic.div (e 0) (rates 0))) &&
          binary64Arithmetic.lt now (binary64Arithmetic.add now (binary64Arithmetic.div (e 0) (rates 0)))) =
          true := ht 0 h0
      have h0' : binary64Arithmetic.lt binary64Arithmetic.zero (rates 0) = true := h0
      have hd : drawExponential binary64Arithmetic (tapeSource Binary64)
          (⟨us, e 0 :: (nrmFloatInitTape (fun j => rates j.succ) (fun j => e j.succ) ++ es)⟩ : Tape Binary64) =
          .ok (e 0, ⟨us, nrmFloatInitTape (fun j => rates j.succ) (fun j => e j.succ) ++ es⟩) := by
        simp only [drawExponential, tapeSource, Bind.bind, Except.bind, he0]
        rfl
      simp only [List.ofFn_succ, h0, ite_true, List.singleton_append, List.cons_append, List.nil_append,
        nrmInitializeAux, h0', hd, Bind.bind, Except.bind, ht0, Bool.not_true, Bool.false_eq_true, ite_false,
        Pure.pure, Except.pure, hi]
      rfl
    · have h0' : binary64Arithmetic.lt binary64Arithmetic.zero (rates 0) = false :=
        Bool.eq_false_of_not_eq_true h0
      have h0'' : binary64Arithmetic.lt 0 (rates 0) = false := Bool.eq_false_of_not_eq_true h0
      simp only [List.ofFn_succ, h0'', Bool.false_eq_true, ite_false, List.nil_append, nrmInitializeAux,
        h0', Bind.bind, Except.bind, Pure.pure, Except.pure, hi]

/-! ### Masked clock schedules -/

/-- Masked FloatLib clocks. Inactive channels hold the finite placeholder `0`, which
the cache never stores. -/
noncomputable def nrmFloatClocksM {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64) : Nat → Fin (n + 1) → Binary64
  | 0 => fun j => if binary64Arithmetic.lt 0 (rates 0 j) then start + e 0 j / rates 0 j else 0
  | k + 1 => fun j =>
    if binary64Arithmetic.lt 0 (rates (k + 1) j) then
      (if (j.val != (marks k).val && binary64Arithmetic.lt 0 (rates k j)) then
        rescaleClock binary64Arithmetic (nrmFloatClocksM rates e marks start k (marks k)) (rates k j)
          (rates (k + 1) j) (nrmFloatClocksM rates e marks start k j)
      else nrmFloatClocksM rates e marks start k (marks k) + e (k + 1) j / rates (k + 1) j)
    else 0

/-- The exact real clocks of the same masked schedule. -/
noncomputable def nrmRealClocksM {n : Nat} (rates : Nat → Fin (n + 1) → Binary64)
    (er : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1)) (start : ℝ) : Nat → Fin (n + 1) → ℝ
  | 0 => fun j => start + er 0 j / floatReal (rates 0 j)
  | k + 1 => fun j => updatedRealClock (rates k) (rates (k + 1)) (nrmRealClocksM rates er marks start k)
      (er (k + 1)) (nrmRealClocksM rates er marks start k (marks k)) (marks k) j

noncomputable def nrmFloatTimesM {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64) : Nat → Binary64
  | 0 => start
  | k + 1 => nrmFloatClocksM rates e marks start k (marks k)

noncomputable def nrmRealTimesM {n : Nat} (rates : Nat → Fin (n + 1) → Binary64)
    (er : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1)) (start : ℝ) : Nat → ℝ
  | 0 => start
  | k + 1 => nrmRealClocksM rates er marks start k (marks k)

noncomputable def nrmFloatCacheM {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64) (k : Nat) : NRMState Binary64 :=
  ⟨Array.ofFn (rates k), Array.ofFn (fun j => if binary64Arithmetic.lt 0 (rates k j) then
    some (nrmFloatClocksM rates e marks start k j) else none)⟩

lemma updateClock_masked {n : Nat} (rates e : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (start : Binary64) (k : Nat) (j : Fin (n + 1)) :
    updateClock binary64Arithmetic (rates k j) (rates (k + 1) j)
      (nrmFloatClocksM rates e marks start k j) (e (k + 1) j)
      (nrmFloatTimesM rates e marks start (k + 1)) j.val (marks k).val =
      if binary64Arithmetic.lt 0 (rates (k + 1) j) then
        some (nrmFloatClocksM rates e marks start (k + 1) j) else none := by
  simp only [updateClock, nrmFloatTimesM, nrmFloatClocksM,
    show binary64Arithmetic.zero = (0 : Binary64) from rfl]
  split_ifs <;> rfl

structure NRMMaskedInitConditions {n : Nat} (rates e : Fin (n + 1) → Binary64)
    (er : Fin (n + 1) → ℝ) (start : Binary64) (sr η : ℝ) : Prop where
  rateValid : ∀ j, validRate binary64Arithmetic (rates j) = true
  startFinite : ExecFloat.Binary.isFinite start = true
  rateNonzero : ∀ j, 0 < floatReal (rates j) → Model.isZero (ExecFloat.Binary.toModel (rates j)) = false
  exponentialValid : ∀ j, 0 < floatReal (rates j) → exponentialFlag (e j) = true
  quotientFinite : ∀ j, 0 < floatReal (rates j) → ExecFloat.Binary.isFinite (e j / rates j) = true
  clockValid : ∀ j, 0 < floatReal (rates j) → clockFlag start (e j) (rates j) = true
  budget : ∀ j, 0 < floatReal (rates j) →
    floatEpsilon (floatReal start + floatReal (e j / rates j)) +
    floatEpsilon (floatReal (e j) / floatReal (rates j)) +
    |floatReal start - sr| + |floatReal (e j) - er j| / floatReal (rates j) ≤ η

/-- Native masked FloatLib initialization and the error of every active clock. -/
theorem nrm_float_initialize_masked {n : Nat} (rates e : Fin (n + 1) → Binary64)
    (er : Fin (n + 1) → ℝ) (start : Binary64) (sr η : ℝ)
    (hc : NRMMaskedInitConditions rates e er start sr η) (us es : List Binary64) :
    nrmInitialize binary64Arithmetic (tapeSource Binary64) (Array.ofFn rates) start
      ⟨us, nrmFloatInitTape rates e ++ es⟩ =
      .ok (⟨Array.ofFn rates, Array.ofFn (fun j => if binary64Arithmetic.lt 0 (rates j) then
        some (start + e j / rates j) else none)⟩, ⟨us, es⟩) ∧
    ∀ j, 0 < floatReal (rates j) →
      |floatReal (start + e j / rates j) - (sr + er j / floatReal (rates j))| ≤ η := by
  have hact : ∀ j, binary64Arithmetic.lt 0 (rates j) = true → 0 < floatReal (rates j) := by
    intro j h
    rw [float_lt_zero_decide _ (finite_of_valid _ (hc.rateValid j))] at h
    exact of_decide_eq_true h
  constructor
  · unfold nrmInitialize
    rw [show checkRates binary64Arithmetic (Array.ofFn rates) = .ok () from
      checkRatesAux_valid _ _ (by
        intro a ha
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (by simpa only [Array.toList_ofFn] using ha)
        exact hc.rateValid j) 0]
    simp only [Bind.bind, Except.bind, show binary64Arithmetic.finite start = true from hc.startFinite,
      Bool.not_true, Bool.false_eq_true, ite_false, Array.toList_ofFn]
    rw [nrmInitializeAux_float_masked rates e start (fun j h => hc.exponentialValid j (hact j h))
      (fun j h => hc.clockValid j (hact j h)) us es]
    simp only [Except.bind, Pure.pure, Except.pure, List.toArray_ofFn]
  · intro j hj
    have hf := finite_of_valid (rates j) (hc.rateValid j)
    have he : ExecFloat.Binary.isFinite (e j) = true := by
      have h := hc.exponentialValid j hj
      rw [exponentialFlag, Bool.and_eq_true] at h
      exact h.1
    have ht : ExecFloat.Binary.isFinite (start + e j / rates j) = true := by
      have h := hc.clockValid j hj
      rw [clockFlag, Bool.and_eq_true] at h
      exact h.1
    have hclock := float_clock_time_error start (e j) (rates j) hc.startFinite he hf
      (hc.rateNonzero j hj) (hc.quotientFinite j hj) ht
    have hsource : |(floatReal start + floatReal (e j) / floatReal (rates j)) -
        (sr + er j / floatReal (rates j))| ≤
        |floatReal start - sr| + |floatReal (e j) - er j| / floatReal (rates j) := by
      have hx : (floatReal start + floatReal (e j) / floatReal (rates j)) -
        (sr + er j / floatReal (rates j)) =
        (floatReal start - sr) + (floatReal (e j) - er j) / floatReal (rates j) := by ring
      rw [hx]
      exact (abs_add_le _ _).trans (by rw [abs_div, abs_of_pos hj])
    exact ((abs_sub_le _ _ _).trans (add_le_add hclock hsource)).trans
      (by simpa only [add_assoc] using hc.budget j hj)

/-! ### Masked trajectory certificate -/

/-- FloatLib NRM numerical certificate with inactive channels and a stop index `m`. -/
structure NRMMaskedConditions {σ : Type} {n : Nat}
    (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Fin (n + 1))
    (rates e : Nat → Fin (n + 1) → Binary64) (er : Nat → Fin (n + 1) → ℝ)
    (hm : ∀ k, mf.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, mf.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ) (fuel cap m : Nat) (save : Bool) : Prop where
  stop : m ≤ fuel + 1
  hv : ∀ l j, validRate binary64Arithmetic (rates l j) = true
  hi : NRMMaskedInitConditions (rates 0) (e 0) (er 0) start sr (η 0)
  hc : ∀ k, k < m → k < fuel → NRMUpdateConditions (rates k) (rates (k + 1))
      (nrmFloatClocksM rates e marks start k) (e (k + 1)) (er (k + 1))
      (nrmFloatTimesM rates e marks start (k + 1)) (η k) (η k) (η (k + 1)) (marks k)
  hcacheFinite : ∀ k, k < m → ∀ j, ExecFloat.Binary.isFinite (nrmFloatClocksM rates e marks start k j) = true
  hactive : ∀ k, k < m → 0 < floatReal (rates k (marks k))
  hgap : ∀ k, k < m → ∀ j, j ≠ marks k → 0 < floatReal (rates k j) →
      nrmRealClocksM rates er marks sr k (marks k) + 2 * η k < nrmRealClocksM rates er marks sr k j
  hinc : ∀ k, k < m → binary64Arithmetic.le (nrmFloatTimesM rates e marks start k)
      (nrmFloatTimesM rates e marks start (k + 1)) = true
  hrinc : ∀ k, k < m → nrmRealTimesM rates er marks sr k ≤ nrmRealTimesM rates er marks sr (k + 1)
  hbudget : ∀ k, k < m → η k ≤ δ
  absorb : m ≤ fuel → ∀ j, binary64Arithmetic.lt 0 (rates m j) = false
  hvalid : (binary64Arithmetic.finite start && binary64Arithmetic.finite hf &&
      binary64Arithmetic.le start hf) = true
  hstart : binary64Arithmetic.lt start hf = true
  hhf : ExecFloat.Binary.isFinite hf = true
  hh : |floatReal hf - hr| ≤ δ
  h0 : |floatReal start - sr| ≤ δ
  hmargin : ∀ k, k < m → 2 * δ < |nrmRealTimesM rates er marks sr (k + 1) - hr|

/-- Every active masked cache error is derived from initialization and prior errors. -/
theorem nrm_float_masked_cache_errors {σ : Type} {n : Nat}
    (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Fin (n + 1))
    (rates e : Nat → Fin (n + 1) → Binary64) (er : Nat → Fin (n + 1) → ℝ)
    (hm : ∀ k, mf.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, mf.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ) (fuel cap m : Nat) (save : Bool)
    (C : NRMMaskedConditions mf mr htransition states marks rates e er hm hs start hf sr hr δ η fuel cap m
      save) :
    ∀ k, k < m → ∀ j, 0 < floatReal (rates k j) →
      |floatReal (nrmFloatClocksM rates e marks start k j) - nrmRealClocksM rates er marks sr k j| ≤ η k := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    have h := (nrm_float_initialize_masked _ _ _ _ _ _ C.hi [] []).2 j hj
    have hact : binary64Arithmetic.lt 0 (rates 0 j) = true := by
      rw [float_lt_zero_decide _ (finite_of_valid _ (C.hv 0 j))]
      exact decide_eq_true hj
    simpa only [nrmFloatClocksM, nrmRealClocksM, hact, ite_true] using h
  | succ k ih =>
    intro hk j hj
    have hkm : k < m := by omega
    have hkf : k < fuel := by have := C.stop; omega
    have hnow : |floatReal (nrmFloatTimesM rates e marks start (k + 1)) -
        nrmRealTimesM rates er marks sr (k + 1)| ≤ η k := ih hkm (marks k) (C.hactive k hkm)
    have cert := (C.hc k hkm hkf).toCertificate _ _ _ _ (nrmRealClocksM rates er marks sr k)
      (er (k + 1)) _ (nrmRealTimesM rates er marks sr (k + 1)) _ _ _ _ hnow
      (fun j hj => ih hkm j hj)
    have hact : binary64Arithmetic.lt 0 (rates (k + 1) j) = true := by
      rw [float_lt_zero_decide _ (finite_of_valid _ (C.hv (k + 1) j))]
      exact decide_eq_true hj
    have h := (nrm_float_update_certificate_refines _ _ _ _ _ _ _ _ _ _ _ _ cert j).2
      (nrmFloatClocksM rates e marks start (k + 1) j)
      (by rw [updateClock_masked]; simp [hact])
    simpa only [nrmRealClocksM, nrmRealTimesM] using h

/-- Complete masked FloatLib NRM trajectory refinement, including inactive channels
and absorbing states, through the actual public driver with any unread tape suffix. -/
theorem nrm_float_masked_trajectory_close {σ : Type} {n : Nat}
    (mf : Model Binary64 σ) (mr : Model ℝ σ)
    (htransition : ∀ x i, mf.transition x i = mr.transition x i)
    (states : Nat → σ) (marks : Nat → Fin (n + 1))
    (rates e : Nat → Fin (n + 1) → Binary64) (er : Nat → Fin (n + 1) → ℝ)
    (hm : ∀ k, mf.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, mf.transition (states k) (marks k).val = .ok (states (k + 1)))
    (start hf : Binary64) (sr hr δ : ℝ) (η : Nat → ℝ) (fuel cap m : Nat) (save : Bool)
    (us es : List Binary64)
    (C : NRMMaskedConditions mf mr htransition states marks rates e er hm hs start hf sr hr δ η fuel cap m
      save) :
    TraceClose δ
      (observeRun (simulate binary64Arithmetic (tapeSource Binary64) mf .nrm (states 0) start hf
        ⟨us, nrmFloatInitTape (rates 0) (e 0) ++ (nrmFloatTape rates e marks 0 fuel ++ es)⟩ fuel save cap))
      (replayEvents realArithmetic mr hr save fuel (states 0) sr 0 #[(sr, states 0)]
        (scheduledEvents (nrmRealTimesM rates er marks sr) (fun k => (marks k).val) 0 m)) := by
  let tf := nrmFloatTimesM rates e marks start
  let tr := nrmRealTimesM rates er marks sr
  let tape := fun k count => (⟨us, nrmFloatTape rates e marks k (count - 1) ++ es⟩ : Tape Binary64)
  let cache := fun k => some (nrmFloatCacheM rates e marks start k)
  have herr := nrm_float_masked_cache_errors mf mr htransition states marks rates e er hm hs start hf sr hr δ
    η fuel cap m save C
  have hrf : ∀ l j, ExecFloat.Binary.isFinite (rates l j) = true := fun l j => finite_of_valid _ (C.hv l j)
  have hnext : ∀ k, k < m → nrmNext binary64Arithmetic (nrmFloatCacheM rates e marks start k) =
      some ⟨tf (k + 1), (marks k).val⟩ := by
    intro k hk
    exact (nrm_float_winner_masked (rates k) (nrmFloatClocksM rates e marks start k)
      (nrmRealClocksM rates er marks sr k) (marks k) (η k) (hrf k) (C.hactive k hk) (C.hcacheFinite k hk)
      (herr k hk) (C.hgap k hk)).1
  have hinitC : initializeCache binary64Arithmetic (tapeSource Binary64) mf .nrm (states 0) (tf 0)
      (⟨us, nrmFloatInitTape (rates 0) (e 0) ++ (nrmFloatTape rates e marks 0 fuel ++ es)⟩ : Tape Binary64) =
      .ok (cache 0, tape 0 (fuel + 1)) := by
    dsimp only [initializeCache]
    dsimp only [tf, nrmFloatTimesM]
    rw [hm 0, (nrm_float_initialize_masked _ _ _ _ _ _ C.hi us (nrmFloatTape rates e marks 0 fuel ++ es)).1]
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, tape, cache, Nat.add_sub_cancel]
    congr 3
    simp only [nrmFloatCacheM, nrmFloatClocksM]
    congr 2
    funext j
    split_ifs <;> rfl
  have hupd : ∀ k count, k < m → k + count + 1 ≤ fuel →
      refreshCache binary64Arithmetic (tapeSource Binary64) mf .nrm (states (k + 1))
        ⟨tf (k + 1), (marks k).val⟩ (tape k (count + 1 + 1)) (cache k) =
        .ok (cache (k + 1), tape (k + 1) (count + 1)) := by
    intro k count hk hkc
    have hkf : k < fuel := by omega
    dsimp only [refreshCache, cache]
    rw [hm (k + 1)]
    simp only [Array.size_ofFn]
    have hex := nrm_float_update_executes (rates k) (rates (k + 1)) (nrmFloatClocksM rates e marks start k)
      (e (k + 1)) (tf (k + 1)) (marks k) (C.hv (k + 1))
      (C.hcacheFinite k hk (marks k)) (C.hc k hk hkf).flags us (nrmFloatTape rates e marks (k + 1) count ++ es)
    have hcl : (fun j => updateClock binary64Arithmetic (rates k j) (rates (k + 1) j)
        (nrmFloatClocksM rates e marks start k j) (e (k + 1) j) (tf (k + 1)) j.val (marks k).val) =
        fun j => if binary64Arithmetic.lt 0 (rates (k + 1) j) then
          some (nrmFloatClocksM rates e marks start (k + 1) j) else none :=
      funext (fun j => updateClock_masked rates e marks start k j)
    rw [hcl] at hex
    change (do
      let result ← nrmUpdate binary64Arithmetic (tapeSource Binary64) (nrmFloatCacheM rates e marks start k)
        (Array.ofFn (rates (k + 1))) (marks k).val (tf (k + 1)) (List.range (n + 1)).toArray
        ⟨us, nrmFloatTape rates e marks k (count + 1) ++ es⟩
      pure (some result.1, result.2)) = _
    rw [nrmFloatTape, List.append_assoc]
    simp only [nrmFloatCacheM] at hex ⊢
    rw [hex]
    rfl
  have hfinite : ∀ k, k < m → ExecFloat.Binary.isFinite (tf (k + 1)) = true := fun k hk =>
    C.hcacheFinite k hk (marks k)
  have herrT : ∀ k, k < m → |floatReal (tf (k + 1)) - tr (k + 1)| ≤ δ := fun k hk =>
    (herr k hk (marks k) (C.hactive k hk)).trans (C.hbudget k hk)
  by_cases hstop : m ≤ fuel
  · apply simulate_float_schedule_close_absorb (tapeSource Binary64) mf mr .nrm htransition states tf tr
      (fun k => (marks k).val) hf hr δ fuel cap m hstop save tape (fun k count => tape k (count + 1)) cache
      (⟨us, nrmFloatInitTape (rates 0) (e 0) ++ (nrmFloatTape rates e marks 0 fuel ++ es)⟩ : Tape Binary64)
      hinitC C.hvalid C.hstart C.hhf C.hh C.h0
    · intro k count hk _
      dsimp only [sampleEvent, cache]
      rw [hnext k hk]
    · intro count _
      refine ⟨tape m (count + 1), ?_⟩
      dsimp only [sampleEvent, cache, nrmFloatCacheM]
      rw [nrm_float_absorbing_cache (rates m) _ (C.absorb hstop)]
    · exact fun k _ => hs k
    · intro k count hk hkc
      exact hupd k count hk hkc.le
    · exact hfinite
    · exact C.hinc
    · exact C.hrinc
    · exact herrT
    · exact C.hmargin
  · have hm' : m = fuel + 1 := le_antisymm C.stop (by omega)
    subst hm'
    apply simulate_float_schedule_close (tapeSource Binary64) mf mr .nrm htransition states tf tr
      (fun k => (marks k).val) hf hr δ fuel cap save tape (fun k count => tape k (count + 1)) cache
      (⟨us, nrmFloatInitTape (rates 0) (e 0) ++ (nrmFloatTape rates e marks 0 fuel ++ es)⟩ : Tape Binary64)
      hinitC C.hvalid C.hstart C.hhf C.hh C.h0
    · intro k count hk
      dsimp only [sampleEvent, cache]
      rw [hnext k (by omega)]
    · exact hs
    · intro k count hk
      exact hupd k count (by omega) hk
    · exact fun k hk => hfinite k (by omega)
    · exact fun k hk => C.hinc k (by omega)
    · exact fun k hk => C.hrinc k (by omega)
    · exact fun k hk => herrT k (by omega)
    · exact fun k hk => C.hmargin k (by omega)

end JumpProcessesLean.Proofs
