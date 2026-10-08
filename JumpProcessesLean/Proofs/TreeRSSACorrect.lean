import JumpProcessesLean.Proofs.TreeRSSAModel
import JumpProcessesLean.Proofs.RSSABranches

/-!
# Tree-RSSA is the native RSSA on the bracket model

In real arithmetic, for every random source, the Tree-RSSA specification makes exactly the
same draws, proposals, acceptances, times, errors and trace as the public `simulate`
driver running the native `rssa` sampler on `bracketModel net`.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA

variable {R : Type}

lemma drawUniform_real_bounds (src : RandomSource ℝ R) (rng : R) (u : ℝ) (r : R)
    (h : drawUniform realArithmetic src rng = .ok (u, r)) : 0 ≤ u ∧ u < 1 := by
  unfold drawUniform at h
  cases hs : src.uniform rng with
  | error e => simp [hs, bind, Except.bind] at h
  | ok p =>
    obtain ⟨u', r'⟩ := p
    simp only [hs, bind, Except.bind] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i hc
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [realArithmetic, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
        not_le, not_lt, Bool.true_and] at hc
      exact ⟨not_lt.mp fun h => hc (Or.inl h), not_le.mp fun h => hc (Or.inr h)⟩

/-- The thinning loops agree: the tree descent proposes what the linear search proposes. -/
theorem proposals_eq_rssaProposals (net : Network ℝ) (src : RandomSource ℝ R) (pop : Array Nat)
    (rates lower upper : Array ℝ) (hu : upper.size = net.reactions.size)
    (hrates : ∀ j < net.reactions.size, rates[j]! = propensity realArithmetic net.reactions[j]! pop)
    (hup : ∀ x ∈ upper.toList, 0 ≤ x) (hpos : 0 < upper.toList.sum) (d : Nat)
    (hd : upper.size ≤ 2 ^ d) (now : ℝ) :
    ∀ fuel elapsed rng,
      TreeRSSA.proposals realArithmetic src net pop lower upper d now upper.toList.sum fuel elapsed rng =
        rssaProposals realArithmetic src rates ⟨lower, upper⟩ now upper.toList.sum fuel elapsed rng := by
  intro fuel
  induction fuel with
  | zero => intro elapsed rng; rfl
  | succ fuel ih =>
    intro elapsed rng
    rw [TreeRSSA.proposals, rssaProposals]
    cases hU : drawUniform realArithmetic src rng with
    | error e => simp [bind, Except.bind]
    | ok p =>
      obtain ⟨u, rng1⟩ := p
      obtain ⟨hu0, hu1⟩ := drawUniform_real_bounds src rng u rng1 hU
      obtain ⟨hlt, hw⟩ := segDescend_eq_weightedIndex upper hup d hd u hu0 hu1 hpos
      rw [sumRates_real] at hw
      simp only [bind, Except.bind]
      rw [show realArithmetic.mul u upper.toList.sum = u * upper.toList.sum from rfl] at hw ⊢
      rw [hw]
      simp only
      have hjM : segDescend realArithmetic upper d 0 (u * upper.toList.sum) < net.reactions.size :=
        hu ▸ hlt
      rw [← hrates _ hjM]
      simp only [decide_eq_true hjM, Bool.true_and, ih]

lemma bracketModel_rates (net : Network ℝ) (st : State) :
    (bracketModel net).rates st = net.reactions.map (propensity realArithmetic · st.pop) := rfl

lemma bracketModel_transition (net : Network ℝ) (st : State) (j : Nat) :
    (bracketModel net).transition st j = .ok (fire net net.maxStoich st j) := rfl

lemma bracketModel_bounds (net : Network ℝ) (st : State) (hb : Bracketed net st) :
    (bracketModel net).bounds st =
      ⟨lowerBounds realArithmetic net st, upperBounds realArithmetic net st⟩ := by
  simp only [bracketModel, hb, ↓reduceIte]

/-- One Tree-RSSA event is one native `rssa` call on the bracket model. -/
theorem event_eq_rssa (net : Network ℝ) (hv : ValidNetwork net) (src : RandomSource ℝ R)
    (st : State) (hb : Bracketed net st) (now : ℝ) (rng : R) (cap : Nat) :
    TreeRSSA.event realArithmetic src net st now rng cap =
      rssa realArithmetic src ((bracketModel net).rates st) ((bracketModel net).bounds st) now rng
        cap := by
  rw [bracketModel_bounds net st hb, bracketModel_rates]
  set rates := net.reactions.map (propensity realArithmetic · st.pop) with hrates
  set lower := lowerBounds realArithmetic net st with hlower
  set upper := upperBounds realArithmetic net st with hupper
  have hrs : rates.size = net.reactions.size := by simp [rates]
  have hls : lower.size = net.reactions.size := by simp [lower, TreeRSSA.lowerBounds]
  have hus : upper.size = net.reactions.size := by simp [upper, TreeRSSA.upperBounds]
  have hvalid : ∀ (i : Nat) (hi : i < rates.size),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega) := by
    intro i hi
    have hi' : i < net.reactions.size := by omega
    have hmem : net.reactions[i] ∈ net.reactions.toList := Array.getElem_mem_toList _
    have hbr := propensity_bracket net hv st hb _ hmem
    simp only [rates, lower, upper, TreeRSSA.lowerBounds, TreeRSSA.upperBounds, Array.getElem_map]
    exact ⟨propensity_nonneg net hv _ hmem _, hbr.1, hbr.2⟩
  have hcheck := checkBounds_real rates ⟨lower, upper⟩ ⟨by simp [hls, hrs], by simp [hus, hrs]⟩ hvalid
  have hup : ∀ x ∈ upper.toList, 0 ≤ x := by
    intro x hx
    simp only [upper, TreeRSSA.upperBounds, Array.toList_map, List.mem_map] at hx
    obtain ⟨rx, hrx, rfl⟩ := hx
    exact propensity_nonneg net hv rx hrx _
  have hd : upper.size ≤ 2 ^ treeDepth net.reactions.size := by
    rw [hus]; exact treeDepth_spec _
  have htotal : segSum realArithmetic upper (treeDepth net.reactions.size) 0 = upper.toList.sum :=
    segSum_root upper _ hd
  have hany : rates.any (realArithmetic.lt realArithmetic.zero) = decide (0 < upper.toList.sum) := by
    rw [Bool.eq_iff_iff, Array.any_eq_true, decide_eq_true_iff, ← enabled_iff_upper_pos net hv st hb]
    constructor
    · rintro ⟨i, hi, h⟩
      have hi' : i < net.reactions.size := by omega
      refine ⟨net.reactions[i], Array.getElem_mem_toList _, ?_⟩
      simpa [rates, realArithmetic] using h
    · rintro ⟨rx, hrx, h⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrx
      have hi' : i < net.reactions.size := by simpa using hi
      exact ⟨i, by omega, by simpa [rates, realArithmetic] using h⟩
  unfold TreeRSSA.event rssa
  rw [hcheck]
  simp only [bind, Except.bind, ← hupper, ← hlower, htotal, sumRates_real, hany]
  by_cases hpos : 0 < upper.toList.sum
  · simp only [realArithmetic, hpos, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    exact proposals_eq_rssaProposals net src st.pop rates lower upper hus
      (fun j hj => by simp [rates, hj]) hup hpos _ hd now cap 0 rng
  · have hle : upper.sum ≤ 0 := by simpa using not_lt.mp hpos
    simp [realArithmetic, hle, pure, Except.pure]

/-- The Tree-RSSA driver loop is the public driver loop with the native `rssa` sampler. -/
theorem simulateLoop_eq (net : Network ℝ) (hv : ValidNetwork net) (src : RandomSource ℝ R)
    (horizon : ℝ) (save : Bool) (cap : Nat) :
    ∀ fuel st now rng count trace, Bracketed net st →
      TreeRSSA.simulateLoop realArithmetic src net net.maxStoich horizon save cap fuel st now rng count
          trace =
        JumpProcessesLean.simulateLoop realArithmetic src (bracketModel net) .rssa horizon save cap fuel
          st now rng none count trace := by
  intro fuel
  induction fuel with
  | zero =>
    intro st now rng count trace hb
    rw [TreeRSSA.simulateLoop, JumpProcessesLean.simulateLoop]
    simp only [sampleEvent]
    rw [event_eq_rssa net hv src st hb]
    rfl
  | succ fuel ih =>
    intro st now rng count trace hb
    have ih' : ∀ j now rng count trace,
        TreeRSSA.simulateLoop realArithmetic src net net.maxStoich horizon save cap fuel
            (fire net net.maxStoich st j) now rng count trace =
          JumpProcessesLean.simulateLoop realArithmetic src (bracketModel net) .rssa horizon save cap
            fuel (fire net net.maxStoich st j) now rng none count trace :=
      fun j now rng count trace => ih _ now rng count trace (fire_bracketed net st j hb)
    rw [TreeRSSA.simulateLoop, JumpProcessesLean.simulateLoop]
    simp only [sampleEvent]
    rw [event_eq_rssa net hv src st hb]
    simp only [bind, Except.bind, refreshCache, bracketModel_transition, pure, Except.pure, ih']
    rfl

/-- **Tree-RSSA is the native RSSA.** In real arithmetic and for every random source, the
Tree-RSSA specification returns exactly what the public driver returns with the native
`rssa` sampler on the bracket model. -/
theorem treeRSSA_simulate_eq (net : Network ℝ) (hv : ValidNetwork net) (src : RandomSource ℝ R)
    (initial : State) (hb : Bracketed net initial) (start horizon : ℝ) (rng : R) (maxEvents : Nat)
    (save : Bool) (cap : Nat) :
    TreeRSSA.simulate realArithmetic src net initial start horizon rng maxEvents save cap =
      JumpProcessesLean.simulate realArithmetic src (bracketModel net) .rssa initial start horizon rng
        maxEvents save cap := by
  unfold TreeRSSA.simulate JumpProcessesLean.simulate
  simp only [initializeCache, bind, Except.bind, pure, Except.pure]
  rw [simulateLoop_eq net hv src horizon save cap maxEvents initial start rng 0 _ hb]

/-! ### The bracket model is consistent -/

section Law

variable {n : Nat}

noncomputable def bracketRates (net : Network ℝ) (hM : net.reactions.size = n + 1) (st : State)
    (j : Fin (n + 1)) : ℝ :=
  propensity realArithmetic (net.reactions[j.val]'(by omega)) st.pop

open Classical in
noncomputable def bracketLower (net : Network ℝ) (hM : net.reactions.size = n + 1) (st : State)
    (j : Fin (n + 1)) : ℝ :=
  if Bracketed net st then propensity realArithmetic (net.reactions[j.val]'(by omega)) st.lo
  else bracketRates net hM st j

open Classical in
noncomputable def bracketUpper (net : Network ℝ) (hM : net.reactions.size = n + 1) (st : State)
    (j : Fin (n + 1)) : ℝ :=
  if Bracketed net st then propensity realArithmetic (net.reactions[j.val]'(by omega)) st.hi
  else bracketRates net hM st j

def bracketTransition (net : Network ℝ) (st : State) (j : Fin (n + 1)) : State :=
  fire net net.maxStoich st j.val

theorem bracketModel_consistency (net : Network ℝ) (hM : net.reactions.size = n + 1)
    (hv : ValidNetwork net) :
    ModelConsistency (bracketModel net) (bracketTransition net) (bracketRates net hM)
      (bracketLower net hM) (bracketUpper net hM) where
  nonnegative x j := propensity_nonneg net hv _ (Array.getElem_mem_toList _) _
  bounds_valid x j := by
    unfold bracketLower bracketUpper
    split_ifs with hb
    · have h := propensity_bracket net hv x hb (net.reactions[j.val]'(by omega))
        (Array.getElem_mem_toList _)
      exact ⟨propensity_nonneg net hv _ (Array.getElem_mem_toList _) _, h.1, h.2⟩
    · exact ⟨propensity_nonneg net hv _ (Array.getElem_mem_toList _) _, le_refl _, le_refl _⟩
  rates_eq x := by
    apply Array.ext
    · simp [bracketModel_rates, hM]
    · intro i h1 h2
      simp [bracketModel_rates, bracketRates]
  bounds_eq x := by
    simp only [bracketModel]
    by_cases hb : Bracketed net x
    · simp only [hb, ↓reduceIte]
      congr 1
      · apply Array.ext
        · simp [TreeRSSA.lowerBounds, hM]
        · intro i h1 h2
          simp [TreeRSSA.lowerBounds, bracketLower, hb]
      · apply Array.ext
        · simp [TreeRSSA.upperBounds, hM]
        · intro i h1 h2
          simp [TreeRSSA.upperBounds, bracketUpper, hb]
    · simp only [hb, ↓reduceIte]
      congr 1
      · apply Array.ext
        · simp [hM]
        · intro i h1 h2
          simp [bracketLower, hb, bracketRates]
      · apply Array.ext
        · simp [hM]
        · intro i h1 h2
          simp [bracketUpper, hb, bracketRates]
  transition_eq x j := rfl

end Law

end JumpProcessesLean.Proofs
