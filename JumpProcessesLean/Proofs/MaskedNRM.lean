import JumpProcessesLean.Proofs.MaskedRace

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma nrmInitializeAux_zero_update (rates : List ℝ) (now : ℝ) (index fired : Nat)
    (rng : Tape ℝ) :
    nrmInitializeAux realArithmetic (tapeSource ℝ) now rates rng =
      nrmUpdateAllAux realArithmetic (tapeSource ℝ) fired now
        (rates.map (fun _ => 0)) (rates.map (fun _ => none)) rates index rng := by
  induction rates generalizing index rng with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, nrmInitializeAux, nrmUpdateAllAux,
      show realArithmetic.lt realArithmetic.zero (0 : ℝ) = false from by simp [realArithmetic], Bool.and_false]
    by_cases ha : realArithmetic.lt realArithmetic.zero a = true
    · simp only [ha, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      cases hd : drawExponential realArithmetic (tapeSource ℝ) rng with
      | error err => simp [Bind.bind, Except.bind]
      | ok p =>
        rcases p with ⟨e, r⟩
        simp only [Bind.bind, Except.bind]
        split
        · rfl
        · simp only [Pure.pure, Except.pure, Except.bind]
          rw [ih]
    · have ha' : realArithmetic.lt realArithmetic.zero a = false := Bool.eq_false_of_not_eq_true ha
      simp only [ha', Bool.not_false, ite_true, Bool.false_eq_true, ite_false,
        Pure.pure, Except.pure, Bind.bind, Except.bind]
      rw [ih]

/-- Initialization consumes precisely the active channels' independent draws.
Inactive ghost uniforms are not put on the random tape. -/
theorem nrmInitialize_masked_executes {n : Nat} (rates u : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ rates j) (hu : ∀ j, u j ∈ Ioo 0 1)
    (now : ℝ) (us es : List ℝ) :
    nrmInitialize realArithmetic (tapeSource ℝ) (Array.ofFn rates) now
      ⟨us, nrmFreshExponentials (fun _ => 0) rates u 0 0 ++ es⟩ =
      .ok (⟨Array.ofFn rates, Array.ofFn (fun j =>
        if 0 < rates j then some (now + exponentialClock (rates j) (u j)) else none)⟩,
        ⟨us, es⟩) := by
  have hrl : ∀ a ∈ (Array.ofFn rates).toList, 0 ≤ a := by
    simp only [Array.toList_ofFn]
    intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha; exact hr j
  unfold nrmInitialize
  rw [checkRates_real _ hrl]
  simp only [Bind.bind, Except.bind, show realArithmetic.finite now = true from rfl, Bool.not_true, Bool.false_eq_true,
    ite_false, Array.toList_ofFn]
  rw [nrmInitializeAux_zero_update _ now 0 0]
  have hm0 : (List.ofFn rates).map (fun _ => (0 : ℝ)) = List.ofFn (fun _ : Fin n => (0 : ℝ)) := by simp [Function.comp_def]
  have hmn : (List.ofFn rates).map (fun _ => (none : Option ℝ)) =
      List.ofFn (fun _ : Fin n => (none : Option ℝ)) := by simp [Function.comp_def]
  rw [hm0, hmn]
  have he := nrmUpdateAllAux_uniform (fun _ : Fin n => 0) rates (fun _ => 0) u hu
    now (fun j h => (lt_irrefl 0 h).elim) 0 0 us es
  simp only [lt_self_iff_false, ite_false, Nat.zero_add] at he
  rw [he]
  simp [Except.bind, Pure.pure, Except.pure, nrmUpdatedClock, List.toArray_ofFn]

lemma nrmNextAux_none_iff (clocks : List (Option ℝ)) (index : Nat) :
    nrmNextAux realArithmetic clocks index = none ↔ ∀ x ∈ clocks, x = none := by
  induction clocks generalizing index with
  | nil => simp [nrmNextAux]
  | cons c rest ih =>
    cases c with
    | none => simp [nrmNextAux, ih]
    | some t =>
      simp only [nrmNextAux]
      cases h : nrmNextAux realArithmetic rest (index + 1) with
      | none => simp
      | some e =>
        by_cases hc : realArithmetic.le t e.time = true <;> simp_all [nrmNextAux]

lemma nrmNextAux_nullable_sound (clocks : List (Option ℝ)) (index : Nat) (e : Event ℝ)
    (he : nrmNextAux realArithmetic clocks index = some e) :
    ∃ (j : Nat) (hj : j < clocks.length), e.reaction = index + j ∧
      clocks[j]'hj = some e.time ∧ ∀ t : ℝ, some t ∈ clocks → e.time ≤ t := by
  induction clocks generalizing index e with
  | nil => simp [nrmNextAux] at he
  | cons c rest ih =>
    cases c with
    | none =>
      obtain ⟨j, hj, hr, ht, hm⟩ := ih (index + 1) e he
      exact ⟨j + 1, by simpa using hj, by omega, by simpa using ht,
        by intro t ht; exact hm t (by simpa using ht)⟩
    | some t =>
      rw [nrmNextAux] at he
      cases hrest : nrmNextAux realArithmetic rest (index + 1) with
      | none =>
        simp only [hrest, Option.some.injEq] at he
        subst e
        refine ⟨0, by simp, by simp, rfl, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · have hxt : x = t := Option.some.inj hx
          subst x
          exact le_refl _
        · have hf := (nrmNextAux_none_iff rest (index + 1)).mp hrest (some x) hx
          contradiction
      | some b =>
        obtain ⟨j, hj, hr, ht, hm⟩ := ih (index + 1) b hrest
        rw [hrest] at he
        simp only [realArithmetic, decide_eq_true_eq] at he
        by_cases htb : t ≤ b.time
        · have heq : e = ⟨t, index⟩ := by simpa [htb] using he.symm
          subst e
          refine ⟨0, by simp, by simp, rfl, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with hx | hx
          · have hxt : x = t := Option.some.inj hx
            subst x
            exact le_refl _
          · exact htb.trans (hm x hx)
        · have heq : e = b := by simpa [htb] using he.symm
          subst e
          refine ⟨j + 1, by simpa using hj, by omega, by simpa using ht, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with hx | hx
          · have hxt : x = t := Option.some.inj hx
            subst x
            exact (lt_of_not_ge htb).le
          · exact hm x hx

/-- The native nullable argmin ignores zero-rate channels, even if their unused
ghost clock is earlier than every active clock. -/
theorem nrmNext_masked_unique {n : Nat} (rates c : Fin n → ℝ) (i : Fin n)
    (hi : 0 < rates i)
    (hmin : ∀ j, j ≠ i → 0 < rates j → c i < c j) :
    nrmNext realArithmetic ⟨Array.ofFn rates,
      Array.ofFn (fun j => if 0 < rates j then some (c j) else none)⟩ = some ⟨c i, i.val⟩ := by
  let clocks := List.ofFn (fun j => if 0 < rates j then some (c j) else none)
  have hin : some (c i) ∈ clocks := List.mem_ofFn.mpr ⟨i, by simp [hi]⟩
  have hn : nrmNextAux realArithmetic clocks 0 ≠ none := by
    intro h
    have hx := (nrmNextAux_none_iff clocks 0).mp h (some (c i)) hin
    contradiction
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hn
  obtain ⟨j, hj, hr, ht, hm⟩ := nrmNextAux_nullable_sound clocks 0 e he
  have hjn : j < n := by simpa [clocks] using hj
  have hjp : 0 < rates ⟨j, hjn⟩ := by
    simp only [clocks, List.getElem_ofFn] at ht
    split at ht
    · assumption
    · contradiction
  have hjt : e.time = c ⟨j, hjn⟩ := by
    simp only [clocks, List.getElem_ofFn, hjp, ite_true, Option.some.injEq] at ht
    exact ht.symm
  have hji : (⟨j, hjn⟩ : Fin n) = i := by
    by_contra h
    have hlt := hmin ⟨j, hjn⟩ h hjp
    have hle := hm (c i) hin
    rw [hjt] at hle
    linarith
  have heq : e = ⟨c i, i.val⟩ := by
    cases e
    simp_all
    exact congrArg Fin.val hji
  unfold nrmNext
  rw [Array.toList_ofFn]
  simpa only [heq] using he

end JumpProcessesLean.Proofs
