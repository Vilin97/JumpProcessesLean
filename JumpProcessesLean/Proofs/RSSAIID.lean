import JumpProcessesLean.Proofs.NRMIID

/-!
# Rejection SSA on IID streams

RSSA proposals consume a data-dependent number of draws: each proposal reads a
selection uniform, an exponential and an acceptance uniform, until the first
acceptance. The first-success block is a stopping reader of the IID streams. With
the public fixed proposal cap `N`, the actual driver agrees with the exact
first-success law outside an explicit event whose probability tends to zero.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal BigOperators Topology

/-! ### Offsets of sequential readers and their tapes -/

/-- Uniform and exponential-source draws consumed by the first `l` readers. -/
noncomputable def readerOffsets {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ) :
    ℕ → Streams → ℕ × ℕ
  | 0, _ => (0, 0)
  | l + 1, ω =>
    let o := readerOffsets r l ω
    let ω' := (readerParse r l ω).2
    (o.1 + (r l).usedU ω', o.2 + (r l).usedV ω')

lemma readerParse_rest_offsets {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ)
    (l : ℕ) (ω : Streams) :
    (readerParse r l ω).2 = streamsDrop (readerOffsets r l ω).1 (readerOffsets r l ω).2 ω := by
  induction l with
  | zero => simp [readerParse, readerOffsets]
  | succ l ih =>
    rw [readerParse_succ, Function.comp_apply]
    simp only [StreamReader.rest, readerOffsets]
    rw [ih, streamsDrop_drop, ← ih]

lemma readerOffsets_mono {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ)
    (k c : ℕ) (ω : Streams) :
    (readerOffsets r k ω).1 ≤ (readerOffsets r (k + c) ω).1 ∧
      (readerOffsets r k ω).2 ≤ (readerOffsets r (k + c) ω).2 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [← Nat.add_assoc]
    simp only [readerOffsets]
    omega

/-- Readers whose packet tape is exactly the block of stream draws they consumed. -/
structure TapeCompatible {σ γ : Type} [MeasurableSpace γ] {n : Nat} {model : Model ℝ σ}
    {algorithm : Algorithm} {states : Nat → σ} {rates : Nat → Fin (n + 1) → ℝ}
    {marks : Nat → Fin (n + 1)} (P : PacketSpecification (γ := γ) model algorithm states rates marks)
    (r : ℕ → StreamReader γ) : Prop where
  uniforms : ∀ l ω, P.uniforms l ((r l).read ω) =
    (List.range ((r l).usedU ω)).map (fun i => ω (.inl i))
  exponentials : ∀ l ω, P.exponentials l ((r l).read ω) =
    (List.range ((r l).usedV ω)).map (fun i => -log (ω (.inr i)))

lemma packetTapeFrom_readers {σ γ : Type} [MeasurableSpace γ] {n : Nat} {model : Model ℝ σ}
    {algorithm : Algorithm} {states : Nat → σ} {rates : Nat → Fin (n + 1) → ℝ}
    {marks : Nat → Fin (n + 1)} (P : PacketSpecification (γ := γ) model algorithm states rates marks)
    (r : ℕ → StreamReader γ) (hc : TapeCompatible P r) (K : ℕ) (ω : Streams) (fallback : γ)
    (tail : Tape ℝ) :
    ∀ c k, k + c ≤ K →
      packetTapeFrom P.uniforms P.exponentials (rawChronological fallback (readerParse r K ω).1)
        tail k c =
        ⟨(List.range ((readerOffsets r (k + c) ω).1 - (readerOffsets r k ω).1)).map
            (fun i => ω (.inl ((readerOffsets r k ω).1 + i))) ++ tail.uniforms,
          (List.range ((readerOffsets r (k + c) ω).2 - (readerOffsets r k ω).2)).map
            (fun i => -log (ω (.inr ((readerOffsets r k ω).2 + i)))) ++ tail.exponentials⟩ := by
  intro c
  induction c with
  | zero => intro k _; simp [packetTapeFrom]
  | succ c ih =>
    intro k hk
    have hsrc : rawChronological fallback (readerParse r K ω).1 k =
        (r k).read (streamsDrop (readerOffsets r k ω).1 (readerOffsets r k ω).2 ω) := by
      simp only [rawChronological, show k < K by omega, dite_true]
      rw [readerParse_chron r K ω k (by omega), readerParse_rest_offsets]
    have hnext := ih (k + 1) (by omega)
    have hmono := readerOffsets_mono r (k + 1) c ω
    have hk1 : readerOffsets r (k + 1) ω =
        ((readerOffsets r k ω).1 + (r k).usedU (streamsDrop (readerOffsets r k ω).1
            (readerOffsets r k ω).2 ω),
          (readerOffsets r k ω).2 + (r k).usedV (streamsDrop (readerOffsets r k ω).1
            (readerOffsets r k ω).2 ω)) := by
      simp only [readerOffsets, readerParse_rest_offsets]
    rw [packetTapeFrom, hnext, hsrc, hc.uniforms, hc.exponentials]
    rw [show k + (c + 1) = k + 1 + c by omega]
    simp only [hk1] at hmono ⊢
    apply Tape.mk.injEq _ _ _ _ |>.mpr
    constructor
    · rw [← List.append_assoc]
      congr 1
      rw [show (readerOffsets r (k + 1 + c) ω).1 - (readerOffsets r k ω).1 =
          (r k).usedU (streamsDrop (readerOffsets r k ω).1 (readerOffsets r k ω).2 ω) +
            ((readerOffsets r (k + 1 + c) ω).1 - ((readerOffsets r k ω).1 +
              (r k).usedU (streamsDrop (readerOffsets r k ω).1 (readerOffsets r k ω).2 ω))) by omega,
        List.range_add, List.map_append, List.map_map]
      simp [streamsDrop, Nat.add_assoc, Function.comp_def]
    · rw [← List.append_assoc]
      congr 1
      rw [show (readerOffsets r (k + 1 + c) ω).2 - (readerOffsets r k ω).2 =
          (r k).usedV (streamsDrop (readerOffsets r k ω).1 (readerOffsets r k ω).2 ω) +
            ((readerOffsets r (k + 1 + c) ω).2 - ((readerOffsets r k ω).2 +
              (r k).usedV (streamsDrop (readerOffsets r k ω).1 (readerOffsets r k ω).2 ω))) by omega,
        List.range_add, List.map_append, List.map_map]
      simp [streamsDrop, Nat.add_assoc, Function.comp_def]

/-! ### Measurable values in sigma types -/

lemma measurable_sigma_of_countable {Ω β : Type} [MeasurableSpace Ω] [Countable β]
    [MeasurableSpace β] [MeasurableSingletonClass β] {X : β → Type} [∀ b, MeasurableSpace (X b)]
    (b : Ω → β) (hb : Measurable b) (x : (c : β) → Ω → X c) (hx : ∀ c, Measurable (x c)) :
    Measurable (fun ω => (⟨b ω, x (b ω) ω⟩ : Σ c, X c)) := by
  intro S hS
  have hS' : ∀ c, MeasurableSet (Sigma.mk c ⁻¹' S) := fun c =>
    MeasurableSpace.measurableSet_iInf.mp hS c
  have hset : (fun ω => (⟨b ω, x (b ω) ω⟩ : Σ c, X c)) ⁻¹' S =
      ⋃ c, (b ⁻¹' {c} ∩ x c ⁻¹' (Sigma.mk c ⁻¹' S)) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro h
      exact ⟨b ω, rfl, h⟩
    · rintro ⟨c, hc, h⟩
      subst hc
      exact h
  rw [hset]
  exact MeasurableSet.iUnion (fun c => (hb (measurableSet_singleton c)).inter (hx c (hS' c)))

/-! ### The RSSA first-success reader -/

/-- Mark of the `j`th proposal: selection uniform `2j`, acceptance uniform `2j+1`. -/
noncomputable def streamProposalMark (R L U : List ℝ) (ω : Streams) (j : ℕ) : Option ℕ :=
  proposalMark R L U (ω (.inl (2 * j)), ω (.inl (2 * j + 1)))

lemma measurable_streamProposalMark (R L U : List ℝ) (j : ℕ) :
    Measurable (fun ω => streamProposalMark R L U ω j) :=
  (measurable_proposalMark R L U).comp (by fun_prop)

/-- Accepted at `j`, or the default index when no proposal is ever accepted. -/
def AcceptOrNone (R L U : List ℝ) (ω : Streams) (j : ℕ) : Prop :=
  streamProposalMark R L U ω j ≠ none ∨ (j = 0 ∧ ∀ i, streamProposalMark R L U ω i = none)

lemma acceptOrNone_exists (R L U : List ℝ) (ω : Streams) : ∃ j, AcceptOrNone R L U ω j := by
  by_cases h : ∃ j, streamProposalMark R L U ω j ≠ none
  · obtain ⟨j, hj⟩ := h
    exact ⟨j, Or.inl hj⟩
  · simp only [not_exists, ne_eq, not_not] at h
    exact ⟨0, Or.inr ⟨rfl, h⟩⟩

open Classical in
/-- Number of rejected proposals before the first acceptance. -/
noncomputable def streamProposalCount (R L U : List ℝ) (ω : Streams) : ℕ :=
  Nat.find (acceptOrNone_exists R L U ω)

lemma measurable_streamProposalCount (R L U : List ℝ) :
    Measurable (streamProposalCount R L U) := by
  classical
  apply measurable_find (acceptOrNone_exists R L U)
  intro k
  have h1 : MeasurableSet {ω : Streams | streamProposalMark R L U ω k ≠ none} :=
    (measurable_streamProposalMark R L U k (measurableSet_singleton none)).compl
  have h2 : MeasurableSet {ω : Streams | ∀ i, streamProposalMark R L U ω i = none} := by
    have : {ω : Streams | ∀ i, streamProposalMark R L U ω i = none} =
        ⋂ i, (fun ω => streamProposalMark R L U ω i) ⁻¹' {none} := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iInter (fun i => measurable_streamProposalMark R L U i (measurableSet_singleton _))
  by_cases hk : k = 0
  · subst hk
    have : {ω : Streams | AcceptOrNone R L U ω 0} =
        {ω | streamProposalMark R L U ω 0 ≠ none} ∪ {ω | ∀ i, streamProposalMark R L U ω i = none} := by
      ext ω; simp [AcceptOrNone]
    rw [this]
    exact h1.union h2
  · have : {ω : Streams | AcceptOrNone R L U ω k} = {ω | streamProposalMark R L U ω k ≠ none} := by
      ext ω; simp [AcceptOrNone, hk]
    rw [this]
    exact h1

lemma streamProposalCount_spec (R L U : List ℝ) (ω : Streams) (k : ℕ)
    (hk : streamProposalMark R L U ω k ≠ none) (hbefore : ∀ j, j < k → streamProposalMark R L U ω j = none) :
    streamProposalCount R L U ω = k := by
  classical
  unfold streamProposalCount
  rw [Nat.find_eq_iff]
  refine ⟨Or.inl hk, fun j hj => ?_⟩
  rintro (h | ⟨_, hall⟩)
  · exact h (hbefore j hj)
  · exact hk (hall k)

lemma streamProposalCount_accepted (R L U : List ℝ) (ω : Streams)
    (hacc : ∃ j, streamProposalMark R L U ω j ≠ none) :
    streamProposalMark R L U ω (streamProposalCount R L U ω) ≠ none ∧
      ∀ j, j < streamProposalCount R L U ω → streamProposalMark R L U ω j = none := by
  classical
  obtain ⟨j0, hj0⟩ := hacc
  have hspec := Nat.find_spec (acceptOrNone_exists R L U ω)
  have hmin := fun j (hj : j < Nat.find (acceptOrNone_exists R L U ω)) =>
    Nat.find_min (acceptOrNone_exists R L U ω) hj
  change streamProposalMark R L U ω (Nat.find (acceptOrNone_exists R L U ω)) ≠ none ∧
    ∀ j, j < Nat.find (acceptOrNone_exists R L U ω) → streamProposalMark R L U ω j = none
  rcases hspec with h | ⟨_, hall⟩
  · refine ⟨h, fun j hj => ?_⟩
    have := hmin j hj
    simp only [AcceptOrNone, not_or, not_and] at this
    by_contra hne
    exact this.1 hne
  · exact absurd (hall j0) hj0

/-- Selected channel of the accepted proposal, as a channel index. -/
noncomputable def streamProposalIndex {n : ℕ} (R L U : List ℝ) (ω : Streams) : Fin (n + 1) :=
  match streamProposalMark R L U ω (streamProposalCount R L U ω) with
  | some i => if h : i < n + 1 then ⟨i, h⟩ else 0
  | none => 0

lemma measurable_streamProposalIndex {n : ℕ} (R L U : List ℝ) :
    Measurable (streamProposalIndex (n := n) R L U) := by
  let g : ℕ → Streams → Fin (n + 1) := fun k ω =>
    match streamProposalMark R L U ω k with
    | some i => if h : i < n + 1 then ⟨i, h⟩ else 0
    | none => 0
  have hg : ∀ k, Measurable (g k) := by
    intro k
    have hc : Measurable (fun o : Option ℕ => (match o with
        | some i => if h : i < n + 1 then (⟨i, h⟩ : Fin (n + 1)) else 0
        | none => 0)) := measurable_of_countable _
    exact hc.comp (measurable_streamProposalMark R L U k)
  have h2 : Measurable (fun p : Streams × ℕ => g p.2 p.1) :=
    measurable_from_prod_countable_left (fun k => hg k)
  exact h2.comp (measurable_id.prodMk (measurable_streamProposalCount R L U))

/-- The first `m` proposals: exponential sources and selection/acceptance pairs. -/
noncomputable def proposalBlock (m : ℕ) (ω : Streams) : (Fin m → ℝ) × (Fin m → ℝ × ℝ) :=
  (fun q => ω (.inr q), fun q => (ω (.inl (2 * q)), ω (.inl (2 * q + 1))))

lemma measurable_proposalBlock (m : ℕ) : Measurable (proposalBlock m) := by
  unfold proposalBlock
  fun_prop

/-- Proposal blocks read from the IID streams are IID. -/
theorem iidStreams_map_proposalBlock (m : ℕ) :
    iidStreams.map (proposalBlock m) =
      (Measure.pi (fun _ : Fin m => unitUniform)).prod
        (Measure.pi (fun _ : Fin m => unitUniform.prod unitUniform)) := by
  let g : Fin m ⊕ (Fin m ⊕ Fin m) → ℕ ⊕ ℕ :=
    Sum.elim (fun q => .inr q) (Sum.elim (fun q => .inl (2 * q)) (fun q => .inl (2 * q + 1)))
  have hg : Function.Injective g := by
    intro x y h
    rcases x with x | x | x <;> rcases y with y | y | y <;>
      simp only [g, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h ⊢
    all_goals first | exact Fin.ext h | omega
  have hsub := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ⊕ ℕ => unitUniform) hg
  rw [Measure.infinitePi_eq_pi (fun _ : Fin m ⊕ (Fin m ⊕ Fin m) => unitUniform)] at hsub
  let e1 := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ (Fin m ⊕ Fin m) => ℝ)
  let e2 := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => ℝ)
  let e3 := (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m)).symm
  have hcomp : proposalBlock m = (Prod.map id (e3 ∘ e2)) ∘ e1 ∘ (fun ω x => ω (g x)) := by
    funext ω
    rfl
  have h1 := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin m ⊕ (Fin m ⊕ Fin m) => unitUniform)).map_eq
  have h2 := (measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => unitUniform)).map_eq
  have h3 := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m) (fun _ => unitUniform)
    (fun _ => unitUniform)).symm.map_eq
  unfold iidStreams
  rw [hcomp, ← Measure.map_map (measurable_id.prodMap (e3.measurable.comp e2.measurable))
    (e1.measurable.comp (by fun_prop)), ← Measure.map_map e1.measurable (by fun_prop), hsub, h1,
    ← Measure.map_prod_map _ _ measurable_id (e3.measurable.comp e2.measurable), Measure.map_id,
    ← Measure.map_map e3.measurable e2.measurable, h2, h3]

lemma iidStreams_all_rejected (R L U : List ℝ)
    (hshape : L.length = R.length ∧ U.length = R.length)
    (hb : ∀ (i : Nat) (hi : i < R.length),
      0 ≤ L[i]'(by omega) ∧ L[i]'(by omega) ≤ R[i] ∧ R[i] ≤ U[i]'(by omega))
    (hA : 0 < R.sum) (N : ℕ) :
    iidStreams {ω | ∀ j, j < N → streamProposalMark R L U ω j = none} =
      ENNReal.ofReal (1 - R.sum / U.sum) ^ N := by
  have hset : {ω : Streams | ∀ j, j < N → streamProposalMark R L U ω j = none} =
      (fun ω => (proposalBlock N ω).2) ⁻¹'
        (Set.univ.pi (fun _ => proposalMark R L U ⁻¹' {none})) := by
    ext ω
    simp only [mem_setOf_eq, mem_preimage, mem_univ_pi, mem_singleton_iff, proposalBlock,
      streamProposalMark]
    exact ⟨fun h q => h q q.isLt, fun h j hj => h ⟨j, hj⟩⟩
  have hpairs : iidStreams.map (fun ω => (proposalBlock N ω).2) =
      Measure.pi (fun _ : Fin N => unitUniform.prod unitUniform) := by
    have h := congrArg (fun μ => μ.map Prod.snd) (iidStreams_map_proposalBlock N)
    simp only [Measure.map_map measurable_snd (measurable_proposalBlock N)] at h
    rw [Measure.map_snd_prod, measure_univ, one_smul] at h
    exact h
  have hm : MeasurableSet (Set.univ.pi (fun _ : Fin N => proposalMark R L U ⁻¹' {none})) :=
    MeasurableSet.univ_pi (fun _ => measurable_proposalMark R L U (measurableSet_singleton _))
  rw [hset, ← Measure.map_apply (f := fun ω => (proposalBlock N ω).2)
    (measurable_snd.comp (measurable_proposalBlock N)) hm, hpairs, Measure.pi_pi]
  simp only [proposalMark_rejection_probability R L U hshape hb hA, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- RSSA first-success reader for one event at fixed (completed) rates and bounds. -/
noncomputable def rssaReader {n : ℕ} (R L U : List ℝ)
    (hshape : L.length = R.length ∧ U.length = R.length)
    (hb : ∀ (i : Nat) (hi : i < R.length),
      0 ≤ L[i]'(by omega) ∧ L[i]'(by omega) ≤ R[i] ∧ R[i] ≤ U[i]'(by omega))
    (hA : 0 < R.sum) (hB : 0 < U.sum) : StreamReader (RSSAStoppingInput (n + 1)) where
  read ω := ⟨(streamProposalCount R L U ω, streamProposalIndex R L U ω),
    proposalBlock (streamProposalCount R L U ω + 1) ω⟩
  usedU ω := 2 * (streamProposalCount R L U ω + 1)
  usedV ω := streamProposalCount R L U ω + 1
  good := {ω | ∃ j, streamProposalMark R L U ω j ≠ none}
  measurable_read := by
    exact measurable_sigma_of_countable
      (fun ω => (streamProposalCount R L U ω, streamProposalIndex R L U ω))
      ((measurable_streamProposalCount R L U).prodMk (measurable_streamProposalIndex R L U))
      (fun c ω => proposalBlock (c.1 + 1) ω) (fun c => measurable_proposalBlock (c.1 + 1))
  measurable_usedU := by
    exact (measurable_of_countable (fun k : ℕ => 2 * (k + 1))).comp
      (measurable_streamProposalCount R L U)
  measurable_usedV := by
    exact (measurable_of_countable (fun k : ℕ => k + 1)).comp
      (measurable_streamProposalCount R L U)
  measurableSet_good := by
    have : {ω : Streams | ∃ j, streamProposalMark R L U ω j ≠ none} =
        ⋃ j, ((fun ω => streamProposalMark R L U ω j) ⁻¹' {none})ᶜ := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iUnion (fun j =>
      (measurable_streamProposalMark R L U j (measurableSet_singleton _)).compl)
  ae_good := by
    rw [ae_iff]
    have hq : ENNReal.ofReal (1 - R.sum / U.sum) < 1 := by
      rw [ENNReal.ofReal_lt_one]
      have : 0 < R.sum / U.sum := div_pos hA hB
      linarith
    refine le_antisymm ?_ bot_le
    apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
    intro N
    rw [← iidStreams_all_rejected R L U hshape hb hA N]
    apply measure_mono
    intro ω hω
    simp only [mem_setOf_eq, not_exists, ne_eq, not_not] at hω ⊢
    exact fun j _ => hω j
  determined := by
    intro ω hω ω' h
    obtain ⟨hk, hbefore⟩ := streamProposalCount_accepted R L U ω hω
    set k := streamProposalCount R L U ω with hkdef
    have hU : ∀ i, i < 2 * (k + 1) → ω' (.inl i) = ω (.inl i) := by
      intro i hi
      have := congrFun (congrArg Prod.fst h) ⟨i, hi⟩
      simpa [streamsTake] using this
    have hV : ∀ i, i < k + 1 → ω' (.inr i) = ω (.inr i) := by
      intro i hi
      have := congrFun (congrArg Prod.snd h) ⟨i, hi⟩
      simpa [streamsTake] using this
    have hmark : ∀ j, j ≤ k → streamProposalMark R L U ω' j = streamProposalMark R L U ω j := by
      intro j hj
      simp only [streamProposalMark, hU (2 * j) (by omega), hU (2 * j + 1) (by omega)]
    have hcount : streamProposalCount R L U ω' = k :=
      streamProposalCount_spec R L U ω' k (by rw [hmark k le_rfl]; exact hk)
        (fun j hj => by rw [hmark j hj.le]; exact hbefore j hj)
    have hgood : ω' ∈ {ω | ∃ j, streamProposalMark R L U ω j ≠ none} :=
      ⟨k, by rw [hmark k le_rfl]; exact hk⟩
    have hindex : streamProposalIndex (n := n) R L U ω' = streamProposalIndex R L U ω := by
      unfold streamProposalIndex
      rw [hcount, hmark k le_rfl]
    have hblock : proposalBlock (k + 1) ω' = proposalBlock (k + 1) ω := by
      simp only [proposalBlock]
      apply Prod.ext
      · funext q
        exact hV q q.isLt
      · funext q
        simp only [hU (2 * q) (by omega), hU (2 * q + 1) (by omega)]
    refine ⟨hgood, ?_, by simp only [hcount], by simp only [hcount]⟩
    rw [hcount, hindex, hblock]

lemma proposalBlock_branch_iff {n : ℕ} (R L U : List ℝ) (hlen : U.length = n + 1)
    (ω : Streams) (k : ℕ) (i : Fin (n + 1)) :
    ((∃ j, streamProposalMark R L U ω j ≠ none) ∧ streamProposalCount R L U ω = k ∧
        streamProposalIndex (n := n) R L U ω = i) ↔
      proposalBlock (k + 1) ω ∈ univ ×ˢ proposalBranch R L U k i.val := by
  have hmem : proposalBlock (k + 1) ω ∈ univ ×ˢ proposalBranch R L U k i.val ↔
      (∀ j, j < k → streamProposalMark R L U ω j = none) ∧
        streamProposalMark R L U ω k = some i.val := by
    simp only [mem_prod, mem_univ, true_and, proposalBranch, mem_univ_pi, mem_preimage,
      mem_singleton_iff, proposalBlock]
    constructor
    · intro h
      refine ⟨fun j hj => ?_, ?_⟩
      · have := h ⟨j, by omega⟩
        simpa [hj, streamProposalMark] using this
      · have := h ⟨k, by omega⟩
        simpa [streamProposalMark] using this
    · rintro ⟨hbefore, hk⟩ j
      by_cases hj : j.val < k
      · simpa [hj, streamProposalMark] using hbefore j hj
      · have hjk : j.val = k := by omega
        simpa [hj, streamProposalMark, hjk] using hk
  rw [hmem]
  constructor
  · rintro ⟨hacc, hcount, hindex⟩
    obtain ⟨hk, hbefore⟩ := streamProposalCount_accepted R L U ω hacc
    rw [hcount] at hk hbefore
    refine ⟨hbefore, ?_⟩
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hk
    have hmb : m < n + 1 := hlen ▸ proposalMark_some_bound R L U _ m hm
    have hi : (⟨m, hmb⟩ : Fin (n + 1)) = i := by
      rw [← hindex]
      unfold streamProposalIndex
      rw [hcount, hm]
      simp [hmb]
    rw [hm, ← hi]
  · rintro ⟨hbefore, hk⟩
    have hacc : ∃ j, streamProposalMark R L U ω j ≠ none := ⟨k, by simp [hk]⟩
    have hcount := streamProposalCount_spec R L U ω k (by simp [hk]) hbefore
    refine ⟨hacc, hcount, ?_⟩
    unfold streamProposalIndex
    rw [hcount, hk]
    simp [i.isLt]

/-- The first-success reader has exactly the primitive RSSA stopping-input law. -/
theorem rssaReader_law {n : ℕ} (R L U : List ℝ) (hlen : U.length = n + 1)
    (hshape : L.length = R.length ∧ U.length = R.length)
    (hb : ∀ (i : Nat) (hi : i < R.length),
      0 ≤ L[i]'(by omega) ∧ L[i]'(by omega) ≤ R[i] ∧ R[i] ≤ U[i]'(by omega))
    (hA : 0 < R.sum) (hB : 0 < U.sum) :
    iidStreams.map (rssaReader (n := n) R L U hshape hb hA hB).read =
      rssaStoppingInputs (n := n + 1) R L U := by
  set r := rssaReader (n := n) R L U hshape hb hA hB with hr
  ext S hS
  rw [Measure.map_apply r.measurable_read hS]
  unfold rssaStoppingInputs
  rw [Measure.sum_apply _ hS]
  have hgood : iidStreams r.goodᶜ = 0 := ae_iff.mp r.ae_good
  let mk : (b : ℕ × Fin (n + 1)) → RSSABranchInput b.1 → RSSAStoppingInput (n + 1) :=
    fun b x => ⟨b, x⟩
  let T : ℕ × Fin (n + 1) → Set Streams := fun b =>
    proposalBlock (b.1 + 1) ⁻¹' ((univ ×ˢ proposalBranch R L U b.1 b.2.val) ∩ mk b ⁻¹' S)
  have hT : ∀ b, MeasurableSet (T b) := fun b =>
    measurable_proposalBlock _ ((MeasurableSet.univ.prod (measurable_proposalBranch _ _ _ _ _)).inter
      (MeasurableSpace.measurableSet_iInf.mp hS b))
  have hdecomp : r.good ∩ r.read ⁻¹' S = ⋃ b, T b := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_iUnion, T]
    constructor
    · rintro ⟨hg, hS'⟩
      refine ⟨(streamProposalCount R L U ω, streamProposalIndex R L U ω), ?_, hS'⟩
      exact (proposalBlock_branch_iff R L U hlen ω _ _).mp ⟨hg, rfl, rfl⟩
    · rintro ⟨b, hbr, hbS⟩
      obtain ⟨hg, hc, hi⟩ := (proposalBlock_branch_iff R L U hlen ω b.1 b.2).mpr hbr
      refine ⟨hg, ?_⟩
      change (⟨(streamProposalCount R L U ω, streamProposalIndex R L U ω),
        proposalBlock (streamProposalCount R L U ω + 1) ω⟩ : RSSAStoppingInput (n + 1)) ∈ S
      rw [hc, hi]
      exact hbS
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro b b' hbb
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    obtain ⟨-, hc1, hi1⟩ := (proposalBlock_branch_iff R L U hlen ω b.1 b.2).mpr h1.1
    obtain ⟨-, hc2, hi2⟩ := (proposalBlock_branch_iff R L U hlen ω b'.1 b'.2).mpr h2.1
    exact hbb (Prod.ext (hc1.symm.trans hc2) (hi1.symm.trans hi2))
  rw [← measure_inter_conull (s := r.read ⁻¹' S) hgood, inter_comm, hdecomp, measure_iUnion hdisj hT]
  congr 1
  funext b
  have hpre : MeasurableSet (mk b ⁻¹' S) := MeasurableSpace.measurableSet_iInf.mp hS b
  rw [Measure.map_apply (measurable_branch_injection b) hS, rssaBranchInputs,
    Measure.restrict_apply hpre, inter_comm, ← Measure.map_apply (measurable_proposalBlock _)
      ((MeasurableSet.univ.prod (measurable_proposalBranch _ _ _ _ _)).inter hpre),
    iidStreams_map_proposalBlock]

/-! ### Generic facts about sequential readers -/

lemma rawWordLaw_univ {γ : Type} [MeasurableSpace γ] (μ : ℕ → Measure γ)
    (hμ : ∀ l, IsProbabilityMeasure (μ l)) (K : ℕ) : rawWordLaw μ K univ = 1 := by
  induction K with
  | zero => simp [rawWordLaw]
  | succ K ih =>
    rw [rawWordLaw, Measure.map_apply (measurable_rawWordExtend K) MeasurableSet.univ, preimage_univ,
      ← univ_prod_univ, Measure.prod_prod, ih, measure_univ, one_mul]

lemma readerParse_rest_law {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ) (l : ℕ) :
    iidStreams.map (fun ω => (readerParse r l ω).2) = iidStreams := by
  have h := congrArg (fun μ => μ.map Prod.snd) (readerParse_law r l)
  simp only [Measure.map_map measurable_snd (measurable_readerParse r l)] at h
  rw [Measure.map_snd_prod, rawWordLaw_univ _ (fun _ => inferInstance), one_smul] at h
  exact h

lemma readerParse_ae_good {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ) (K : ℕ) :
    ∀ᵐ ω ∂iidStreams, ∀ l, l < K → (readerParse r l ω).2 ∈ (r l).good := by
  rw [ae_all_iff]
  intro l
  by_cases hl : l < K
  · have h := (r l).ae_good
    rw [← readerParse_rest_law r l] at h
    have h2 := (ae_map_iff (p := fun ω => ω ∈ (r l).good)
      (measurable_readerParse r l).snd.aemeasurable (r l).measurableSet_good).mp h
    filter_upwards [h2] with ω hω _
    exact hω
  · exact Filter.Eventually.of_forall (fun _ h => absurd h hl)

lemma readerParse_law_fst {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ) (K : ℕ) :
    iidStreams.map (fun ω => (readerParse r K ω).1) = rawWordLaw (fun l => iidStreams.map (r l).read) K := by
  have h := congrArg (fun μ => μ.map Prod.fst) (readerParse_law r K)
  simp only [Measure.map_map measurable_fst (measurable_readerParse r K)] at h
  rw [Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

lemma flatMap_proposal_pairs : ∀ (m : ℕ) (x : Fin m → ℝ) (f : ℕ → ℝ),
    (List.ofFn (fun j : Fin m => (x j, (f (2 * j), f (2 * j + 1))))).flatMap
      (fun p : ℝ × (ℝ × ℝ) => [p.2.1, p.2.2]) = (List.range (2 * m)).map f
  | 0, _, _ => by simp
  | m + 1, x, f => by
    rw [List.ofFn_succ, List.flatMap_cons]
    have ih := flatMap_proposal_pairs m (fun j => x j.succ) (fun i => f (2 + i))
    have hpairs : (fun j : Fin m => (x j.succ, (f (2 * (j.succ : ℕ)), f (2 * (j.succ : ℕ) + 1)))) =
        (fun j : Fin m => (x j.succ, (f (2 + 2 * (j : ℕ)), f (2 + (2 * (j : ℕ) + 1))))) := by
      funext j
      simp only [Fin.val_succ]
      congr 3 <;> omega
    rw [hpairs, ih, show 2 * (m + 1) = 2 + 2 * m by ring, List.range_add, List.map_append,
      List.map_map]
    simp [List.range_succ, Function.comp_def]

/-! ### RSSA reaction-word branches of the IID streams -/

section RSSAWords

variable {σ : Type} {n : ℕ} (transition : σ → Fin (n + 1) → σ)
  (rates lower upper : σ → Fin (n + 1) → ℝ)
  (hb : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j) (initial : σ)

/-- First-success reader at a fixed state, using completed rates and bounds. -/
noncomputable def rssaStateReader (x : σ) : StreamReader (RSSAStoppingInput (n + 1)) :=
  rssaReader (n := n) (List.ofFn (completedRates (rates x)))
    (List.ofFn (completedLower (rates x) (lower x))) (List.ofFn (completedUpper (rates x) (upper x)))
    (completed_rssa_data _ _ _ (hb x)).1 (completed_rssa_data _ _ _ (hb x)).2.1
    (completed_rssa_data _ _ _ (hb x)).2.2.1 (completed_rssa_data _ _ _ (hb x)).2.2.2.1

/-- First-success readers along a reaction word. -/
noncomputable def rssaWordReaders {K : ℕ} (w : Fin K → Fin (n + 1)) :
    ℕ → StreamReader (RSSAStoppingInput (n + 1)) := fun l =>
  rssaStateReader rates lower upper hb (stateAlongWord transition initial (extendMarks w) l)

/-- First-success blocks read along a reaction word, most recent first. -/
noncomputable def rssaWordParse {K : ℕ} (w : Fin K → Fin (n + 1)) (ω : Streams) :
    Fin K → RSSAStoppingInput (n + 1) :=
  (readerParse (rssaWordReaders transition rates lower upper hb initial w) K ω).1

/-- The streams realize reaction word `w`. -/
noncomputable def rssaWordEvent {K : ℕ} (w : Fin K → Fin (n + 1)) : Set Streams :=
  rssaWordParse transition rates lower upper hb initial w ⁻¹'
    (Set.univ.pi (fun q : Fin K => {p | rssaStoppingMark p = extendMarks w (K - 1 - q)}))

/-- Every first-success block along `w` uses at most `N` proposals. -/
noncomputable def rssaWordCapEvent {K : ℕ} (w : Fin K → Fin (n + 1)) (N : ℕ) : Set Streams :=
  rssaWordParse transition rates lower upper hb initial w ⁻¹'
    (Set.univ.pi (fun _ : Fin K => {p : RSSAStoppingInput (n + 1) | p.1.1 < N}))

/-- All `fuel + 1` first-success blocks of the realized word fit in the proposal cap. -/
noncomputable def rssaCapGood (fuel N : ℕ) : Set Streams :=
  ⋃ w : Fin (fuel + 1) → Fin (n + 1),
    rssaWordEvent transition rates lower upper hb initial w ∩
      rssaWordCapEvent transition rates lower upper hb initial w N

/-- Probability that some first-success block needs more than the proposal cap. -/
noncomputable def rssaCapDefect (fuel N : ℕ) : ℝ≥0∞ :=
  iidStreams (rssaCapGood transition rates lower upper hb initial fuel N)ᶜ

lemma measurable_rssaWordParse {K : ℕ} (w : Fin K → Fin (n + 1)) :
    Measurable (rssaWordParse transition rates lower upper hb initial w) :=
  (measurable_readerParse _ K).fst

lemma measurableSet_rssaMarkSet {n : ℕ} (i : Fin (n + 1)) :
    MeasurableSet {p : RSSAStoppingInput (n + 1) | rssaStoppingMark p = i} :=
  measurable_rssaStoppingMark _ (measurableSet_singleton i)

lemma measurableSet_rssaCountSet {n : ℕ} (N : ℕ) :
    MeasurableSet {p : RSSAStoppingInput (n + 1) | p.1.1 < N} := by
  have h : Measurable (fun p : RSSAStoppingInput (n + 1) => p.1.1) :=
    measurable_stopping_function _ (fun _ => by dsimp only; exact measurable_const)
  exact h measurableSet_Iio

lemma measurableSet_rssaWordEvent {K : ℕ} (w : Fin K → Fin (n + 1)) :
    MeasurableSet (rssaWordEvent transition rates lower upper hb initial w) :=
  measurable_rssaWordParse transition rates lower upper hb initial w
    (MeasurableSet.univ_pi (fun _ => measurableSet_rssaMarkSet _))

lemma measurableSet_rssaWordCapEvent {K : ℕ} (w : Fin K → Fin (n + 1)) (N : ℕ) :
    MeasurableSet (rssaWordCapEvent transition rates lower upper hb initial w N) :=
  measurable_rssaWordParse transition rates lower upper hb initial w
    (MeasurableSet.univ_pi (fun _ => measurableSet_rssaCountSet N))

lemma rssaWordParse_law {K : ℕ} (w : Fin K → Fin (n + 1)) :
    iidStreams.map (rssaWordParse transition rates lower upper hb initial w) =
      rawWordLaw (fun l => rssaStoppingInputs (n := n + 1)
        (List.ofFn (completedRates (rates (stateAlongWord transition initial (extendMarks w) l))))
        (List.ofFn (completedLower (rates (stateAlongWord transition initial (extendMarks w) l))
          (lower (stateAlongWord transition initial (extendMarks w) l))))
        (List.ofFn (completedUpper (rates (stateAlongWord transition initial (extendMarks w) l))
          (upper (stateAlongWord transition initial (extendMarks w) l))))) K := by
  unfold rssaWordParse
  rw [readerParse_law_fst]
  congr 1
  funext l
  simp only [rssaWordReaders, rssaStateReader]
  rw [rssaReader_law _ _ _ (by simp)]

/-- The realized-word branch has exactly the primitive RSSA word measure. -/
lemma rssaWordEvent_branch {K : ℕ} (w : Fin K → Fin (n + 1)) :
    (iidStreams.restrict (rssaWordEvent transition rates lower upper hb initial w)).map
      (rssaWordParse transition rates lower upper hb initial w) =
      rawWordLaw (fun l => rssaPacketInputs
        (rates (stateAlongWord transition initial (extendMarks w) l))
        (lower (stateAlongWord transition initial (extendMarks w) l))
        (upper (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w l)) K := by
  unfold rssaWordEvent
  rw [← Measure.restrict_map (measurable_rssaWordParse _ _ _ _ hb _ w)
    (MeasurableSet.univ_pi (fun _ => measurableSet_rssaMarkSet _)), rssaWordParse_law,
    ← rawWordLaw_restrict _ (fun l => by
      have h := completed_rssa_data (rates (stateAlongWord transition initial (extendMarks w) l))
        (lower (stateAlongWord transition initial (extendMarks w) l))
        (upper (stateAlongWord transition initial (extendMarks w) l)) (hb _)
      have := rssa_stopping_inputs_probability (n := n + 1) _ _ _ (by simp) h.1 h.2.1 h.2.2.1
        h.2.2.2.1 h.2.2.2.2
      infer_instance)
      _ (fun l => measurableSet_rssaMarkSet _)]
  rfl

lemma rssaWordEvent_cap_branch {K : ℕ} (w : Fin K → Fin (n + 1)) (N : ℕ) :
    (iidStreams.restrict (rssaWordEvent transition rates lower upper hb initial w ∩
        rssaWordCapEvent transition rates lower upper hb initial w N)).map
      (rssaWordParse transition rates lower upper hb initial w) =
      (rawWordLaw (fun l => rssaPacketInputs
        (rates (stateAlongWord transition initial (extendMarks w) l))
        (lower (stateAlongWord transition initial (extendMarks w) l))
        (upper (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w l)) K).restrict
          (Set.univ.pi (fun _ : Fin K => {p : RSSAStoppingInput (n + 1) | p.1.1 < N})) := by
  rw [← rssaWordEvent_branch transition rates lower upper hb initial w,
    Measure.restrict_map (measurable_rssaWordParse _ _ _ _ hb _ w)
      (MeasurableSet.univ_pi (fun _ => measurableSet_rssaCountSet N)),
    Measure.restrict_restrict ((measurable_rssaWordParse _ _ _ _ hb _ w)
      (MeasurableSet.univ_pi (fun _ => measurableSet_rssaCountSet N))), inter_comm]
  rfl

include hb in
/-- Holding times of the realized-word branch have the target law. -/
lemma rssaWord_holding_law {K : ℕ} (w : Fin K → Fin (n + 1)) :
    (rawWordLaw (fun l => rssaPacketInputs
        (rates (stateAlongWord transition initial (extendMarks w) l))
        (lower (stateAlongWord transition initial (extendMarks w) l))
        (upper (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w l)) K).map
      (rawWordHoldings (fun l => rssaStoppingTime (List.ofFn (completedUpper
        (rates (stateAlongWord transition initial (extendMarks w) l))
        (upper (stateAlongWord transition initial (extendMarks w) l))))) K) =
    targetWordLaw (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks w) l)))
      (extendMarks w) K := by
  rw [raw_word_holding_law _ (fun l => rssa_packet_finite _ _ _ (hb _) _) _
    (fun l => measurable_rssaStoppingTime _)]
  have h (k : Nat) : independentWordLaw (fun l => (rssaPacketInputs
        (rates (stateAlongWord transition initial (extendMarks w) l))
        (lower (stateAlongWord transition initial (extendMarks w) l))
        (upper (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w l)).map
      (rssaStoppingTime (List.ofFn (completedUpper
        (rates (stateAlongWord transition initial (extendMarks w) l))
        (upper (stateAlongWord transition initial (extendMarks w) l)))))) k =
      targetWordLaw (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks w) l)))
        (extendMarks w) k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [independentWordLaw, targetWordLaw, ih, rssa_packet_clock_law _ _ _ (hb _)]
  exact h K

lemma rssaWordEvent_mass {K : ℕ} (w : Fin K → Fin (n + 1)) :
    iidStreams (rssaWordEvent transition rates lower upper hb initial w) =
      pathWordWeight transition rates initial w := by
  have h1 : iidStreams (rssaWordEvent transition rates lower upper hb initial w) =
      ((iidStreams.restrict (rssaWordEvent transition rates lower upper hb initial w)).map
        (rssaWordParse transition rates lower upper hb initial w)) univ := by
    rw [Measure.map_apply (measurable_rssaWordParse _ _ _ _ hb _ w) MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
  rw [h1, rssaWordEvent_branch, ← preimage_univ (f := rawWordHoldings _ K),
    ← Measure.map_apply (measurable_rawWordHoldings _ (fun l => measurable_rssaStoppingTime _) K)
      MeasurableSet.univ, rssaWord_holding_law transition rates lower upper hb initial w,
    target_word_mass _ (fun l => completedRates_positive_total _)]
  unfold pathWordWeight
  apply Finset.prod_congr rfl
  intro q _
  simp only [extendMarks, q.isLt, dite_true]

lemma rssaWordEvent_total (K : ℕ) (hr : ∀ x j, 0 ≤ rates x j) :
    ∑ w : Fin K → Fin (n + 1), iidStreams (rssaWordEvent transition rates lower upper hb initial w) = 1 := by
  simp_rw [rssaWordEvent_mass]
  exact path_word_weights_normalize transition rates hr K initial

lemma rssaWordParse_chron {K : ℕ} (w : Fin K → Fin (n + 1)) (ω : Streams) (l : ℕ) (hl : l < K) :
    rssaWordParse transition rates lower upper hb initial w ω ⟨K - 1 - l, by omega⟩ =
      (rssaStateReader rates lower upper hb (stateAlongWord transition initial (extendMarks w) l)).read
        (readerParse (rssaWordReaders transition rates lower upper hb initial w) l ω).2 :=
  readerParse_chron _ K ω l hl

lemma rssaWordEvent_disjoint (K : ℕ) :
    Pairwise (Function.onFun Disjoint
      (fun w : Fin K → Fin (n + 1) => rssaWordEvent transition rates lower upper hb initial w)) := by
  intro w w' hww
  rw [Function.onFun, Set.disjoint_left]
  intro ω hω hω'
  apply hww
  apply words_eq_of_sequential_choice
  intro l hl hprev
  have hmarks : ∀ j, j < l → extendMarks w j = extendMarks w' j :=
    extendMarks_agree w w' l (fun j hj hjK => hprev j hj)
  have hstates : ∀ m, m ≤ l → stateAlongWord transition initial (extendMarks w) m =
      stateAlongWord transition initial (extendMarks w') m := fun m hm =>
    stateAlongWord_congr transition initial _ _ m (fun j hj => hmarks j (by omega))
  have hreaders : readerParse (rssaWordReaders transition rates lower upper hb initial w) l =
      readerParse (rssaWordReaders transition rates lower upper hb initial w') l :=
    readerParse_congr _ _ l (fun m hm => by simp only [rssaWordReaders, hstates m hm.le])
  have h1 := (Set.mem_univ_pi.mp hω) ⟨K - 1 - l, by omega⟩
  have h2 := (Set.mem_univ_pi.mp hω') ⟨K - 1 - l, by omega⟩
  have hq : K - 1 - (⟨K - 1 - l, by omega⟩ : Fin K).val = l := by simp only; omega
  simp only [hq, mem_ofPred_eq] at h1 h2
  rw [rssaWordParse_chron _ _ _ _ _ _ _ _ _ hl] at h1 h2
  rw [hreaders, hstates l le_rfl] at h1
  rw [h1] at h2
  have hmw : extendMarks w l = w ⟨l, hl⟩ := by simp [extendMarks, hl]
  have hmw' : extendMarks w' l = w' ⟨l, hl⟩ := by simp [extendMarks, hl]
  rw [← hmw, ← hmw', h2]

end RSSAWords

/-! ### The public capped RSSA driver -/

lemma rssaWord_tapeCompatible {σ : Type} {n : Nat} (model : Model ℝ σ)
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper) (initial : σ) {K : ℕ}
    (w : Fin K → Fin (n + 1)) :
    TapeCompatible (rssaPacketSpecification model
      (stateAlongWord transition initial (extendMarks w))
      (fun l => rates (stateAlongWord transition initial (extendMarks w) l))
      (fun l => lower (stateAlongWord transition initial (extendMarks w) l))
      (fun l => upper (stateAlongWord transition initial (extendMarks w) l)) (extendMarks w)
      (fun l j => C.bounds_valid _ j) (fun l => C.rates_eq _) (fun l => C.bounds_eq _))
      (rssaWordReaders transition rates lower upper C.bounds_valid initial w) where
  uniforms := by
    intro l ω
    simp only [rssaPacketSpecification, rssaWordReaders, rssaStateReader, rssaReader, proposalBlock,
      proposalUniforms]
    exact flatMap_proposal_pairs _ _ (fun i => ω (.inl i))
  exponentials := by
    intro l ω
    simp only [rssaPacketSpecification, rssaWordReaders, rssaStateReader, rssaReader, proposalBlock,
      proposalExponentials, List.map_ofFn, Function.comp_def]
    exact ofFn_eq_range_map _ (fun i => -log (ω (.inr i)))

lemma rssaWord_offsets_bound {σ : Type} {n : Nat} (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (hb : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j) (initial : σ)
    {K : ℕ} (w : Fin K → Fin (n + 1)) (N : ℕ) (ω : Streams)
    (hcap : ω ∈ rssaWordCapEvent transition rates lower upper hb initial w N) :
    ∀ k, k ≤ K →
      (readerOffsets (rssaWordReaders transition rates lower upper hb initial w) k ω).1 ≤ 2 * N * k ∧
      (readerOffsets (rssaWordReaders transition rates lower upper hb initial w) k ω).2 ≤ N * k := by
  intro k
  induction k with
  | zero => simp [readerOffsets]
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hc := (Set.mem_univ_pi.mp hcap) ⟨K - 1 - k, by omega⟩
    simp only [mem_ofPred_eq] at hc
    have hchron := rssaWordParse_chron transition rates lower upper hb initial w ω k (by omega)
    rw [hchron] at hc
    simp only [readerOffsets, rssaWordReaders, rssaStateReader, rssaReader] at hprev hc ⊢
    constructor <;> nlinarith

/-- On a realized word whose blocks fit in the cap, the public capped RSSA driver
executes the exact first-success transcript read from the IID streams. -/
theorem rssa_capped_driver_executes {σ : Type} {n : Nat} (model : Model ℝ σ)
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper) (initial : σ)
    (start horizon : ℝ) (hstart : start < horizon) (fuel N : ℕ) (saveEvents : Bool) (a b : ℕ)
    (ha : 2 * N * (fuel + 1) ≤ a) (hbN : N * (fuel + 1) ≤ b)
    (w : Fin (fuel + 1) → Fin (n + 1)) (ω : Streams) (hω : ∀ x, ω x ∈ Ioo (0 : ℝ) 1)
    (hgood : ∀ l, l < fuel + 1 →
      (readerParse (rssaWordReaders transition rates lower upper C.bounds_valid initial w) l ω).2 ∈
        (rssaWordReaders transition rates lower upper C.bounds_valid initial w l).good)
    (hE : ω ∈ rssaWordEvent transition rates lower upper C.bounds_valid initial w)
    (hcap : ω ∈ rssaWordCapEvent transition rates lower upper C.bounds_valid initial w N) :
    let states := stateAlongWord transition initial (extendMarks w)
    let P := rssaPacketSpecification model states (fun l => rates (states l))
      (fun l => lower (states l)) (fun l => upper (states l)) (extendMarks w)
      (fun l j => C.bounds_valid _ j) (fun l => C.rates_eq _) (fun l => C.bounds_eq _)
    observeRun (simulate realArithmetic (tapeSource ℝ) model .rssa initial start horizon
      (streamTape a b ω) fuel saveEvents N) =
    holdingSimulationObservation model states (fun l => rates (states l)) (extendMarks w) start horizon
      fuel saveEvents (rawWordHoldings P.clock (fuel + 1)
        (rssaWordParse transition rates lower upper C.bounds_valid initial w ω)) := by
  intro states P
  let r := rssaWordReaders transition rates lower upper C.bounds_valid initial w
  let parse := rssaWordParse transition rates lower upper C.bounds_valid initial w ω
  let fallback : RSSAStoppingInput (n + 1) := ⟨(0, 0), (fun _ => 1 / 2, fun _ => (1 / 2, 1 / 2))⟩
  -- Every packet satisfies the native execution conditions.
  have hgoodP : RawWordGood P.good (fuel + 1) parse := by
    apply rawWordGood_of_index
    intro q
    set l := fuel + 1 - 1 - q.val with hl
    have hlK : l < (fuel + 1) := by omega
    have hq : q = ⟨fuel + 1 - 1 - l, by omega⟩ := Fin.ext (by simp only [hl]; omega)
    have hchron := rssaWordParse_chron transition rates lower upper C.bounds_valid initial w ω l hlK
    have hmark := (Set.mem_univ_pi.mp hE) q
    simp only [mem_ofPred_eq] at hmark
    rw [hq] at hmark ⊢
    change RSSAPacketGood _ _ _ _ (parse ⟨fuel + 1 - 1 - l, by omega⟩)
    simp only [parse] at hmark ⊢
    rw [hchron] at hmark ⊢
    have hlist := completed_rssa_data (rates (states l)) (lower (states l)) (upper (states l))
      (C.bounds_valid _)
    set ω' := (readerParse r l ω).2 with hω'
    have hω'good : ω' ∈ (rssaStateReader rates lower upper C.bounds_valid (states l)).good :=
      hgood l hlK
    have hbranch := (proposalBlock_branch_iff (n := n) _ _ _ (by simp) ω'
      (streamProposalCount _ _ _ ω') (streamProposalIndex _ _ _ ω')).mp ⟨hω'good, rfl, rfl⟩
    have hcoord : ∀ x, ω' x ∈ Ioo (0 : ℝ) 1 := by
      intro x
      rw [hω', readerParse_rest_offsets]
      exact hω _
    refine ⟨⟨fun j => hcoord _, fun j => ⟨hcoord _, hcoord _⟩, hbranch.2⟩, ?_⟩
    have hidx : fuel + 1 - 1 - (fuel + 1 - 1 - l) = l := by omega
    rw [hidx] at hmark
    exact hmark
  have hcost : ∀ k, k ≤ fuel → P.cost k (rawChronological fallback parse k) ≤ N := by
    intro k hk
    have hc := (Set.mem_univ_pi.mp hcap) ⟨fuel + 1 - 1 - k, by omega⟩
    simp only [mem_ofPred_eq] at hc
    simp only [rawChronological, show k < (fuel + 1) by omega, dite_true]
    change (parse ⟨fuel + 1 - 1 - k, by omega⟩).1.1 + 1 ≤ N
    exact Nat.succ_le_of_lt hc
  -- The finite tape is the consumed transcript followed by unread draws.
  have hoff := rssaWord_offsets_bound transition rates lower upper C.bounds_valid initial w N ω hcap (fuel + 1) le_rfl
  set OU := (readerOffsets r (fuel + 1) ω).1 with hOU
  set OV := (readerOffsets r (fuel + 1) ω).2 with hOV
  have hOUa : OU ≤ a := hoff.1.trans ha
  have hOVb : OV ≤ b := hoff.2.trans hbN
  let tail : Tape ℝ := ⟨(List.range (a - OU)).map (fun i => ω (.inl (OU + i))),
    (List.range (b - OV)).map (fun i => -log (ω (.inr (OV + i))))⟩
  have htape : streamTape a b ω =
      packetTapeFrom P.uniforms P.exponentials (rawChronological fallback parse) tail 0 (fuel + 1) := by
    show streamTape a b ω = packetTapeFrom P.uniforms P.exponentials
      (rawChronological fallback (readerParse r (fuel + 1) ω).1) tail 0 (fuel + 1)
    rw [packetTapeFrom_readers P r (rssaWord_tapeCompatible model transition rates lower upper C initial w)
      (fuel + 1) ω fallback tail (fuel + 1) 0 (by omega)]
    have h0 : readerOffsets r 0 ω = (0, 0) := rfl
    simp only [h0, Nat.sub_zero, zero_add]
    rw [← hOU, ← hOV]
    simp only [streamTape, tail]
    rw [ofFn_eq_range_map a (fun i => ω (.inl i)), ofFn_eq_range_map b (fun i => -log (ω (.inr i)))]
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hOUa
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hOVb
    rw [hc, hd, List.range_add, List.range_add, List.map_append, List.map_append, List.map_map,
      List.map_map, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    rfl
  rw [htape]
  exact packet_driver_executes_from model .rssa states (fun l => rates (states l)) (extendMarks w) P
    fallback (fun l => C.transition_eq _ _) start horizon hstart fuel N saveEvents parse hgoodP hcost tail

/-- The proposal-cap defect vanishes: the realized first-success blocks are finite. -/
theorem rssaCapDefect_tendsto_zero {σ : Type} {n : ℕ} (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (hb : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j)
    (initial : σ) (fuel : ℕ) :
    Tendsto (fun N => rssaCapDefect transition rates lower upper hb initial fuel N) atTop (𝓝 0) := by
  let E := fun w : Fin (fuel + 1) → Fin (n + 1) => rssaWordEvent transition rates lower upper hb initial w
  let good := fun N => rssaCapGood transition rates lower upper hb initial fuel N
  have hgoodM : ∀ N, MeasurableSet (good N) := fun N =>
    MeasurableSet.iUnion (fun w => (measurableSet_rssaWordEvent _ _ _ _ hb _ w).inter
      (measurableSet_rssaWordCapEvent _ _ _ _ hb _ w N))
  have hanti : Antitone (fun N => (good N)ᶜ) := by
    intro N M hNM
    apply compl_subset_compl.mpr
    intro ω hω
    simp only [good, rssaCapGood, mem_iUnion] at hω ⊢
    obtain ⟨w, hE, hC⟩ := hω
    refine ⟨w, hE, ?_⟩
    intro q _
    exact lt_of_lt_of_le (hC q (mem_univ q)) hNM
  have hunion : (⋂ N, (good N)ᶜ) = (⋃ w, E w)ᶜ := by
    rw [← compl_iUnion]
    congr 1
    ext ω
    simp only [mem_iUnion, good, rssaCapGood, mem_inter_iff]
    constructor
    · rintro ⟨N, w, hE, _⟩
      exact ⟨w, hE⟩
    · rintro ⟨w, hE⟩
      let M := ∑ q : Fin (fuel + 1),
        ((rssaWordParse transition rates lower upper hb initial w ω q).1.1 + 1)
      refine ⟨M, w, hE, ?_⟩
      intro q _
      have hle := Finset.single_le_sum (f := fun q : Fin (fuel + 1) =>
        (rssaWordParse transition rates lower upper hb initial w ω q).1.1 + 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
      simp only [mem_ofPred_eq]
      omega
  have hr : ∀ x j, 0 ≤ rates x j := fun x j => (hb x j).1.trans (hb x j).2.1
  have hfull : iidStreams (⋃ w, E w) = 1 := by
    rw [measure_iUnion (rssaWordEvent_disjoint _ _ _ _ hb _ (fuel + 1))
      (fun w => measurableSet_rssaWordEvent _ _ _ _ hb _ w), tsum_fintype]
    exact rssaWordEvent_total _ _ _ _ hb _ (fuel + 1) hr
  have hnull : iidStreams (⋃ w, E w)ᶜ = 0 := by
    rw [measure_compl (MeasurableSet.iUnion (fun w => measurableSet_rssaWordEvent _ _ _ _ hb _ w))
      (measure_ne_top _ _), hfull, measure_univ, tsub_self]
  have h := tendsto_measure_iInter_atTop (μ := iidStreams)
    (fun N => (hgoodM N).compl.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hunion, hnull] at h
  exact h

/-- Public fixed-cap RSSA on IID streams. On the event that every first-success block
fits in the cap, its law is bounded by the target law; the remaining mass is the
explicit proposal-cap defect, which tends to zero by `rssaCapDefect_tendsto_zero`. -/
theorem rssa_iid_capped_simulation_law {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (transition : σ → Fin (n + 1) → σ)
    (rates lower upper : σ → Fin (n + 1) → ℝ)
    (C : ModelConsistency model transition rates lower upper)
    (initial : σ) (start horizon : ℝ) (hstart : start < horizon)
    (fuel N : Nat) (saveEvents : Bool) (a b : Nat)
    (ha : 2 * N * (fuel + 1) ≤ a) (hbN : N * (fuel + 1) ≤ b)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : ∀ word : Fin (fuel + 1) → Fin (n + 1),
      let marks := extendMarks word
      let states := stateAlongWord transition initial marks
      Measurable (fun ts => observable (holdingSimulationObservation model states
        (fun l => rates (states l)) marks start horizon fuel saveEvents ts))) :
    let F := fun ω => observable (observeRun (simulate realArithmetic (tapeSource ℝ) model .rssa
      initial start horizon (streamTape a b ω) fuel saveEvents N))
    let good := rssaCapGood transition rates lower upper C.bounds_valid initial fuel N
    let δ := rssaCapDefect transition rates lower upper C.bounds_valid initial fuel N
    let target := targetSimulationLaw model transition rates initial start horizon fuel saveEvents observable
    (iidStreams.restrict good).map F ≤ target ∧
    (∀ S, MeasurableSet S → target S ≤ (iidStreams.restrict good).map F S + δ) ∧
    (∀ S, MeasurableSet S → target S ≤ iidStreams (F ⁻¹' S) + δ ∧
      iidStreams (F ⁻¹' S) ≤ target S + δ) := by
  intro F good δ target
  let hbv := C.bounds_valid
  let E := fun w : Fin (fuel + 1) → Fin (n + 1) => rssaWordEvent transition rates lower upper hbv initial w
  let Cap := fun w : Fin (fuel + 1) → Fin (n + 1) =>
    rssaWordCapEvent transition rates lower upper hbv initial w N
  let parse := fun w : Fin (fuel + 1) → Fin (n + 1) =>
    rssaWordParse transition rates lower upper hbv initial w
  let states := fun w : Fin (fuel + 1) → Fin (n + 1) => stateAlongWord transition initial (extendMarks w)
  let clock := fun (w : Fin (fuel + 1) → Fin (n + 1)) l =>
    rssaStoppingTime (n := n + 1) (List.ofFn (completedUpper (rates (states w l)) (upper (states w l))))
  let G := fun (w : Fin (fuel + 1) → Fin (n + 1)) ω => observable (holdingSimulationObservation model
    (states w) (fun l => rates (states w l)) (extendMarks w) start horizon fuel saveEvents
      (rawWordHoldings (clock w) (fuel + 1) (parse w ω)))
  have hmclock : ∀ w, Measurable (rawWordHoldings (clock w) (fuel + 1)) := fun w =>
    measurable_rawWordHoldings _ (fun l => measurable_rssaStoppingTime _) _
  have hG : ∀ w, Measurable (G w) := fun w =>
    (hobs w).comp ((hmclock w).comp (measurable_rssaWordParse transition rates lower upper hbv initial w))
  have hEM : ∀ w, MeasurableSet (E w) := fun w => measurableSet_rssaWordEvent _ _ _ _ hbv _ w
  have hECM : ∀ w, MeasurableSet (E w ∩ Cap w) := fun w =>
    (hEM w).inter (measurableSet_rssaWordCapEvent _ _ _ _ hbv _ w N)
  have hgoodM : MeasurableSet good := MeasurableSet.iUnion hECM
  have hdisjE := rssaWordEvent_disjoint transition rates lower upper hbv initial (fuel + 1)
  have hdisjEC : Pairwise (Function.onFun Disjoint (fun w => E w ∩ Cap w)) := fun w w' h =>
    Disjoint.mono inter_subset_left inter_subset_left (hdisjE h)
  have hFG : ∀ w, F =ᵐ[iidStreams.restrict (E w ∩ Cap w)] G w := by
    intro w
    rw [Filter.EventuallyEq, ae_restrict_iff' (hECM w)]
    filter_upwards [iidStreams_ae_mem_Ioo,
      readerParse_ae_good (rssaWordReaders transition rates lower upper hbv initial w) (fuel + 1)]
      with ω hω hgood hmem
    exact congrArg observable (rssa_capped_driver_executes model transition rates lower upper C initial
      start horizon hstart fuel N saveEvents a b ha hbN w ω hω hgood hmem.1 hmem.2)
  -- Target law and the capped law as sums over realized words.
  have htargetw : ∀ w, (iidStreams.restrict (E w)).map (G w) =
      (targetWordLaw (fun l => completedRates (rates (states w l))) (extendMarks w) (fuel + 1)).map
        (fun ts => observable (holdingSimulationObservation model (states w)
          (fun l => rates (states w l)) (extendMarks w) start horizon fuel saveEvents ts)) := by
    intro w
    have h1 := Measure.map_map (μ := iidStreams.restrict (E w)) (hobs w)
      ((hmclock w).comp (measurable_rssaWordParse transition rates lower upper hbv initial w))
    have h2 := Measure.map_map (μ := iidStreams.restrict (E w)) (hmclock w)
      (measurable_rssaWordParse transition rates lower upper hbv initial w)
    rw [← h2, rssaWordEvent_branch transition rates lower upper hbv initial w,
      rssaWord_holding_law transition rates lower upper hbv initial w] at h1
    exact h1.symm
  have htarget : target = Measure.sum (fun w => (iidStreams.restrict (E w)).map (G w)) := by
    simp only [target, targetSimulationLaw]
    congr 1
    funext w
    rw [htargetw]
  have hlaw : (iidStreams.restrict good).map F =
      Measure.sum (fun w => (iidStreams.restrict (E w ∩ Cap w)).map (G w)) := by
    have hres : iidStreams.restrict good = Measure.sum (fun w => iidStreams.restrict (E w ∩ Cap w)) :=
      Measure.restrict_iUnion hdisjEC hECM
    rw [hres, Measure.map_sum (aemeasurable_sum_measure_iff.mpr
      (fun w => (hG w).aemeasurable.congr (hFG w).symm))]
    congr 1
    funext w
    exact Measure.map_congr (hFG w)
  have hpiece : ∀ w (S : Set X), MeasurableSet S →
      (iidStreams.restrict (E w ∩ Cap w)).map (G w) S ≤ (iidStreams.restrict (E w)).map (G w) S ∧
      (iidStreams.restrict (E w)).map (G w) S ≤
        (iidStreams.restrict (E w ∩ Cap w)).map (G w) S + iidStreams (E w \ Cap w) := by
    intro w S hS
    rw [Measure.map_apply (hG w) hS, Measure.map_apply (hG w) hS,
      Measure.restrict_apply' (hECM w), Measure.restrict_apply' (hEM w)]
    constructor
    · exact measure_mono (inter_subset_inter_right _ inter_subset_left)
    · calc iidStreams (G w ⁻¹' S ∩ E w)
          ≤ iidStreams ((G w ⁻¹' S ∩ E w) ∩ Cap w) + iidStreams ((G w ⁻¹' S ∩ E w) \ Cap w) :=
            measure_le_inter_add_diff _ _ _
        _ ≤ iidStreams (G w ⁻¹' S ∩ (E w ∩ Cap w)) + iidStreams (E w \ Cap w) := by
            rw [inter_assoc]
            exact add_le_add le_rfl (measure_mono (diff_subset_diff_left inter_subset_right))
  have hdefect : ∑ w, iidStreams (E w \ Cap w) ≤ δ := by
    have hU := measure_iUnion (μ := iidStreams) (f := fun w => E w \ Cap w)
      (fun w w' h => Disjoint.mono diff_subset diff_subset (hdisjE h))
      (fun w => (hEM w).diff (measurableSet_rssaWordCapEvent transition rates lower upper hbv initial w N))
    rw [tsum_fintype] at hU
    rw [← hU]
    apply measure_mono
    intro ω hω
    simp only [mem_iUnion, mem_diff] at hω
    obtain ⟨w, hEw, hCw⟩ := hω
    simp only [good, rssaCapGood, mem_compl_iff, mem_iUnion, mem_inter_iff, not_exists, not_and]
    intro w' hEw' hCw'
    by_cases hww : w' = w
    · subst hww
      exact hCw hCw'
    · exact (Set.disjoint_left.mp (hdisjE hww)) hEw' hEw
  have hupper : (iidStreams.restrict good).map F ≤ target := by
    rw [hlaw, htarget, Measure.le_iff]
    intro S hS
    rw [Measure.sum_apply _ hS, Measure.sum_apply _ hS]
    exact ENNReal.tsum_le_tsum (fun w => (hpiece w S hS).1)
  have hlower : ∀ S, MeasurableSet S → target S ≤ (iidStreams.restrict good).map F S + δ := by
    intro S hS
    rw [hlaw, htarget, Measure.sum_apply _ hS, Measure.sum_apply _ hS, tsum_fintype, tsum_fintype]
    calc ∑ w, (iidStreams.restrict (E w)).map (G w) S
        ≤ ∑ w, ((iidStreams.restrict (E w ∩ Cap w)).map (G w) S + iidStreams (E w \ Cap w)) :=
          Finset.sum_le_sum (fun w _ => (hpiece w S hS).2)
      _ = ∑ w, (iidStreams.restrict (E w ∩ Cap w)).map (G w) S + ∑ w, iidStreams (E w \ Cap w) :=
          Finset.sum_add_distrib
      _ ≤ _ := add_le_add le_rfl hdefect
  have hFae : AEMeasurable F (iidStreams.restrict good) := by
    have hres : iidStreams.restrict good = Measure.sum (fun w => iidStreams.restrict (E w ∩ Cap w)) :=
      Measure.restrict_iUnion hdisjEC hECM
    rw [hres]
    exact aemeasurable_sum_measure_iff.mpr (fun w => (hG w).aemeasurable.congr (hFG w).symm)
  have hgoodapply : ∀ S, MeasurableSet S →
      (iidStreams.restrict good).map F S = iidStreams (F ⁻¹' S ∩ good) := by
    intro S hS
    rw [Measure.map_apply_of_aemeasurable hFae hS, Measure.restrict_apply' hgoodM]
  refine ⟨hupper, hlower, fun S hS => ⟨?_, ?_⟩⟩
  · calc target S ≤ (iidStreams.restrict good).map F S + δ := hlower S hS
      _ ≤ iidStreams (F ⁻¹' S) + δ := by
          rw [hgoodapply S hS]
          exact add_le_add (measure_mono inter_subset_left) le_rfl
  · calc iidStreams (F ⁻¹' S) ≤ iidStreams (F ⁻¹' S ∩ good) + iidStreams (F ⁻¹' S \ good) :=
          measure_le_inter_add_diff _ _ _
      _ ≤ (iidStreams.restrict good).map F S + δ := by
          rw [hgoodapply S hS]
          exact add_le_add le_rfl (measure_mono (fun ω hω => hω.2))
      _ ≤ target S + δ := add_le_add (hupper S) le_rfl

end JumpProcessesLean.Proofs
