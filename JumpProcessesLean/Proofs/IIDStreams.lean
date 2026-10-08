import JumpProcessesLean.Proofs.IndependentRawPath
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent uniform streams

The ideal random input of a simulation consists of two independent infinite IID
Uniform(0,1) streams. `Sum.inl i` is the `i`th uniform draw and `Sum.inr i` is the
uniform transformed into the `i`th exponential draw. This file proves the
regeneration property used after the simulator consumes a data-dependent block of
draws: the remaining streams are again IID and independent of the consumed block.
-/

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

/-- Uniform draws are indexed by `Sum.inl`, exponential-source draws by `Sum.inr`. -/
abbrev Streams := ℕ ⊕ ℕ → ℝ

/-- Two independent infinite IID Uniform(0,1) streams. -/
noncomputable def iidStreams : Measure Streams :=
  Measure.infinitePi (fun _ : ℕ ⊕ ℕ => unitUniform)

instance iidStreams_probability : IsProbabilityMeasure iidStreams := by
  unfold iidStreams
  infer_instance

/-- The first `a` uniform draws and the first `b` exponential-source draws. -/
def streamsTake (a b : ℕ) (ω : Streams) : (Fin a → ℝ) × (Fin b → ℝ) :=
  (fun i => ω (.inl i), fun i => ω (.inr i))

/-- The streams after `a` uniform and `b` exponential-source draws. -/
def streamsDrop (a b : ℕ) (ω : Streams) : Streams :=
  fun x => ω (Sum.map (a + ·) (b + ·) x)

/-- Streams with prescribed prefixes and zero tails. -/
def streamsJoin (a b : ℕ) (q : (Fin a → ℝ) × (Fin b → ℝ)) : Streams :=
  Sum.elim (fun i => if h : i < a then q.1 ⟨i, h⟩ else 0)
    (fun i => if h : i < b then q.2 ⟨i, h⟩ else 0)

@[fun_prop]
lemma measurable_streamsTake (a b : ℕ) : Measurable (streamsTake a b) := by
  unfold streamsTake
  fun_prop

@[fun_prop]
lemma measurable_streamsDrop (a b : ℕ) : Measurable (streamsDrop a b) := by
  unfold streamsDrop
  fun_prop

lemma measurable_streamsJoin (a b : ℕ) : Measurable (streamsJoin a b) := by
  apply Measurable.of_eval
  intro x
  cases x with
  | inl i =>
    by_cases h : i < a
    · simp only [streamsJoin, Sum.elim_inl, h, dite_true]
      fun_prop
    · simp only [streamsJoin, Sum.elim_inl, h, dite_false]
      fun_prop
  | inr i =>
    by_cases h : i < b
    · simp only [streamsJoin, Sum.elim_inr, h, dite_true]
      fun_prop
    · simp only [streamsJoin, Sum.elim_inr, h, dite_false]
      fun_prop

@[simp] lemma streamsTake_join (a b : ℕ) (q : (Fin a → ℝ) × (Fin b → ℝ)) :
    streamsTake a b (streamsJoin a b q) = q := by
  rcases q with ⟨u, v⟩
  simp [streamsTake, streamsJoin]

lemma streamsDrop_drop (a b c d : ℕ) (ω : Streams) :
    streamsDrop c d (streamsDrop a b ω) = streamsDrop (a + c) (b + d) ω := by
  funext x
  cases x <;> simp [streamsDrop, Nat.add_assoc]

@[simp] lemma streamsDrop_zero (ω : Streams) : streamsDrop 0 0 ω = ω := by
  funext x
  cases x <;> simp [streamsDrop]

theorem iidStreams_map_take (a b : ℕ) :
    iidStreams.map (streamsTake a b) =
      (Measure.pi (fun _ : Fin a => unitUniform)).prod (Measure.pi (fun _ : Fin b => unitUniform)) := by
  have hinj : Function.Injective (Sum.map (fun i : Fin a => (i : ℕ)) (fun i : Fin b => (i : ℕ))) :=
    Sum.map_injective.mpr ⟨Fin.val_injective, Fin.val_injective⟩
  have hsub := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ⊕ ℕ => unitUniform) hinj
  rw [Measure.infinitePi_eq_pi (fun _ : Fin a ⊕ Fin b => unitUniform)] at hsub
  have hsplit := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin a ⊕ Fin b => unitUniform)).map_eq
  have hcomp : streamsTake a b = (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)) ∘
      (fun ω (x : Fin a ⊕ Fin b) => ω (Sum.map (fun i : Fin a => (i : ℕ))
        (fun i : Fin b => (i : ℕ)) x)) := by
    funext ω
    rfl
  unfold iidStreams
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop), hsub, hsplit]

theorem iidStreams_map_drop (a b : ℕ) : iidStreams.map (streamsDrop a b) = iidStreams := by
  have hinj : Function.Injective (Sum.map (a + ·) (b + ·)) :=
    Sum.map_injective.mpr ⟨fun x y h => by simpa using h, fun x y h => by simpa using h⟩
  unfold iidStreams streamsDrop
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ⊕ ℕ => unitUniform) hinj

theorem streamsTake_indep_streamsDrop (a b : ℕ) :
    IndepFun (streamsTake a b) (streamsDrop a b) iidStreams := by
  let m : ℕ ⊕ ℕ → MeasurableSpace Streams := fun x => (borel ℝ).comap (fun ω : Streams => ω x)
  let S : Set (ℕ ⊕ ℕ) := {x | Sum.elim (· < a) (· < b) x}
  have hcoord : iIndepFun (fun x (ω : Streams) => ω x) iidStreams := by
    unfold iidStreams
    exact iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have hindep : iIndep m iidStreams := (iIndepFun_iff_iIndep _ _ _).mp hcoord
  have hle : ∀ x, m x ≤ MeasurableSpace.pi := fun x => (measurable_pi_apply x).comap_le
  have hST : Disjoint S Sᶜ := disjoint_compl_right
  have hsplit := indep_iSup_of_disjoint hle hindep hST
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hsplit ?_) ?_
  · apply Measurable.comap_le
    have h1 : Measurable[⨆ x ∈ S, m x] (fun ω : Streams => fun i : Fin a => ω (.inl i)) := by
      refine @Measurable.of_eval Streams (Fin a) (fun _ => ℝ) (⨆ x ∈ S, m x) _ _ ?_
      intro i
      have hi : (Sum.inl (i : ℕ) : ℕ ⊕ ℕ) ∈ S := i.isLt
      have hm : Measurable[m (.inl i)] (fun ω : Streams => ω (.inl i)) := comap_measurable _
      exact hm.mono (le_iSup₂ (f := fun x (_ : x ∈ S) => m x) _ hi) le_rfl
    have h2 : Measurable[⨆ x ∈ S, m x] (fun ω : Streams => fun i : Fin b => ω (.inr i)) := by
      refine @Measurable.of_eval Streams (Fin b) (fun _ => ℝ) (⨆ x ∈ S, m x) _ _ ?_
      intro i
      have hi : (Sum.inr (i : ℕ) : ℕ ⊕ ℕ) ∈ S := i.isLt
      have hm : Measurable[m (.inr i)] (fun ω : Streams => ω (.inr i)) := comap_measurable _
      exact hm.mono (le_iSup₂ (f := fun x (_ : x ∈ S) => m x) _ hi) le_rfl
    exact h1.prodMk h2
  · apply Measurable.comap_le
    refine @Measurable.of_eval Streams (ℕ ⊕ ℕ) (fun _ => ℝ) (⨆ x ∈ Sᶜ, m x) _ _ ?_
    intro x
    have hx : Sum.map (a + ·) (b + ·) x ∈ Sᶜ := by
      cases x <;> simp [S]
    have hm : Measurable[m (Sum.map (a + ·) (b + ·) x)]
        (fun ω : Streams => ω (Sum.map (a + ·) (b + ·) x)) := comap_measurable _
    exact hm.mono (le_iSup₂ (f := fun y (_ : y ∈ Sᶜ) => m y) _ hx) le_rfl

/-- Splitting the streams after finitely many draws. -/
theorem iidStreams_split (a b : ℕ) :
    iidStreams.map (fun ω => (streamsTake a b ω, streamsDrop a b ω)) =
      ((Measure.pi (fun _ : Fin a => unitUniform)).prod
        (Measure.pi (fun _ : Fin b => unitUniform))).prod iidStreams := by
  rw [(streamsTake_indep_streamsDrop a b).map_prod_eq_prod_map_map
    (measurable_streamsTake a b).aemeasurable (measurable_streamsDrop a b).aemeasurable,
    iidStreams_map_take, iidStreams_map_drop]

lemma iidStreams_take_drop_inter (a b : ℕ) {C : Set ((Fin a → ℝ) × (Fin b → ℝ))}
    {B : Set Streams} (hC : MeasurableSet C) (hB : MeasurableSet B) :
    iidStreams (streamsTake a b ⁻¹' C ∩ streamsDrop a b ⁻¹' B) =
      iidStreams (streamsTake a b ⁻¹' C) * iidStreams B := by
  have h := (streamsTake_indep_streamsDrop a b).measure_inter_preimage_eq_mul C B hC hB
  rw [h, ← Measure.map_apply (measurable_streamsDrop a b) hB, iidStreams_map_drop]

/-- A stopping reader consumes a data-dependent number of draws. Its output and
consumption are determined by the consumed prefixes, on a full-measure set. -/
structure StreamReader (γ : Type) [MeasurableSpace γ] where
  read : Streams → γ
  usedU : Streams → ℕ
  usedV : Streams → ℕ
  good : Set Streams
  measurable_read : Measurable read
  measurable_usedU : Measurable usedU
  measurable_usedV : Measurable usedV
  measurableSet_good : MeasurableSet good
  ae_good : ∀ᵐ ω ∂iidStreams, ω ∈ good
  determined : ∀ ω ∈ good, ∀ ω', streamsTake (usedU ω) (usedV ω) ω' =
      streamsTake (usedU ω) (usedV ω) ω →
    ω' ∈ good ∧ read ω' = read ω ∧ usedU ω' = usedU ω ∧ usedV ω' = usedV ω

namespace StreamReader

variable {γ : Type} [MeasurableSpace γ]

/-- The unread part of the streams. -/
def rest (r : StreamReader γ) (ω : Streams) : Streams :=
  streamsDrop (r.usedU ω) (r.usedV ω) ω

lemma measurable_rest (r : StreamReader γ) : Measurable r.rest := by
  have h : Measurable (fun p : Streams × (ℕ × ℕ) => streamsDrop p.2.1 p.2.2 p.1) :=
    measurable_from_prod_countable_left (fun y => by exact measurable_streamsDrop y.1 y.2)
  exact h.comp (measurable_id.prodMk (r.measurable_usedU.prodMk r.measurable_usedV))

/-- The block where the reader consumes exactly `a` uniform and `b` exponential draws. -/
def block (r : StreamReader γ) (A : Set γ) (a b : ℕ) : Set Streams :=
  {ω | ω ∈ r.good ∧ r.usedU ω = a ∧ r.usedV ω = b ∧ r.read ω ∈ A}

lemma measurableSet_block (r : StreamReader γ) {A : Set γ} (hA : MeasurableSet A) (a b : ℕ) :
    MeasurableSet (r.block A a b) :=
  r.measurableSet_good.inter ((r.measurable_usedU (measurableSet_singleton a)).inter
    ((r.measurable_usedV (measurableSet_singleton b)).inter (r.measurable_read hA)))

lemma block_eq_preimage (r : StreamReader γ) (A : Set γ) (a b : ℕ) :
    r.block A a b = streamsTake a b ⁻¹' {q | streamsJoin a b q ∈ r.block A a b} := by
  ext ω
  simp only [mem_preimage, mem_ofPred_eq]
  constructor
  · rintro hω
    rcases hω with ⟨hg, ha, hb, hr⟩
    have hd := r.determined ω hg (streamsJoin a b (streamsTake a b ω))
      (by rw [ha, hb, streamsTake_join])
    exact ⟨hd.1, hd.2.2.1.trans ha, hd.2.2.2.trans hb, hd.2.1 ▸ hr⟩
  · rintro ⟨hg, ha, hb, hr⟩
    have hd := r.determined _ hg ω (by rw [ha, hb, streamsTake_join])
    exact ⟨hd.1, hd.2.2.1.trans ha, hd.2.2.2.trans hb, hd.2.1 ▸ hr⟩

lemma block_pairwise_disjoint (r : StreamReader γ) (A : Set γ) :
    Pairwise (Function.onFun Disjoint (fun ab : ℕ × ℕ => r.block A ab.1 ab.2)) := by
  intro x y hxy
  rw [Function.onFun, Set.disjoint_left]
  rintro ω ⟨_, hxa, hxb, _⟩ ⟨_, hya, hyb, _⟩
  exact hxy (Prod.ext (hxa.symm.trans hya) (hxb.symm.trans hyb))

lemma good_inter_eq_iUnion (r : StreamReader γ) (A : Set γ) :
    r.good ∩ r.read ⁻¹' A = ⋃ ab : ℕ × ℕ, r.block A ab.1 ab.2 := by
  ext ω
  simp only [mem_inter_iff, mem_preimage, mem_iUnion, block, mem_ofPred_eq]
  constructor
  · rintro ⟨hg, hr⟩
    exact ⟨(r.usedU ω, r.usedV ω), hg, rfl, rfl, hr⟩
  · rintro ⟨_, hg, _, _, hr⟩
    exact ⟨hg, hr⟩

/-- Regeneration: after a stopping reader, the unread streams are again IID and
independent of the value that was read. -/
theorem regenerate (r : StreamReader γ) :
    iidStreams.map (fun ω => (r.read ω, r.rest ω)) =
      (iidStreams.map r.read).prod iidStreams := by
  symm
  apply Measure.prod_eq
  intro A B hA hB
  rw [Measure.map_apply (r.measurable_read.prodMk r.measurable_rest) (hA.prod hB),
    Measure.map_apply r.measurable_read hA]
  have hgood : iidStreams r.goodᶜ = 0 := ae_iff.mp r.ae_good
  have hfirst : iidStreams ((fun ω => (r.read ω, r.rest ω)) ⁻¹' A ×ˢ B) =
      ∑' ab : ℕ × ℕ, iidStreams (r.block A ab.1 ab.2 ∩ streamsDrop ab.1 ab.2 ⁻¹' B) := by
    have hset : r.good ∩ ((fun ω => (r.read ω, r.rest ω)) ⁻¹' A ×ˢ B) =
        ⋃ ab : ℕ × ℕ, (r.block A ab.1 ab.2 ∩ streamsDrop ab.1 ab.2 ⁻¹' B) := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_iUnion, block, mem_ofPred_eq, rest]
      constructor
      · rintro ⟨hg, hr, hd⟩
        exact ⟨(r.usedU ω, r.usedV ω), ⟨hg, rfl, rfl, hr⟩, hd⟩
      · rintro ⟨ab, ⟨hg, ha, hb, hr⟩, hd⟩
        exact ⟨hg, hr, by rw [ha, hb]; exact hd⟩
    rw [← measure_inter_conull (s := (fun ω => (r.read ω, r.rest ω)) ⁻¹' A ×ˢ B) hgood, inter_comm,
      hset, measure_iUnion]
    · intro x y hxy
      exact Disjoint.mono inter_subset_left inter_subset_left (r.block_pairwise_disjoint A hxy)
    · intro ab
      exact (r.measurableSet_block hA _ _).inter (measurable_streamsDrop _ _ hB)
  have hsecond : iidStreams (r.read ⁻¹' A) = ∑' ab : ℕ × ℕ, iidStreams (r.block A ab.1 ab.2) := by
    rw [← measure_inter_conull (s := r.read ⁻¹' A) hgood, inter_comm,
      r.good_inter_eq_iUnion A, measure_iUnion (r.block_pairwise_disjoint A)
        (fun ab => r.measurableSet_block hA _ _)]
  rw [hfirst, hsecond, ← ENNReal.tsum_mul_right]
  congr 1
  funext ab
  have hC : MeasurableSet {q | streamsJoin ab.1 ab.2 q ∈ r.block A ab.1 ab.2} :=
    (r.measurableSet_block hA _ _).preimage (measurable_streamsJoin _ _)
  rw [r.block_eq_preimage A ab.1 ab.2, iidStreams_take_drop_inter _ _ hC hB]

end StreamReader

/-- Sequential reading by a family of stopping readers. The values are stored
most recent first, as in `rawWordLaw`; the second component is the unread stream. -/
noncomputable def readerParse {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ) :
    (K : ℕ) → Streams → (Fin K → γ) × Streams
  | 0, ω => (fun q => Fin.elim0 q, ω)
  | K + 1, ω =>
    let p := readerParse r K ω
    (rawWordExtend (p.1, (r K).read p.2), (r K).rest p.2)

lemma readerParse_succ {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ) (K : ℕ) :
    readerParse r (K + 1) = (fun p : (Fin K → γ) × Streams =>
      (rawWordExtend (p.1, (r K).read p.2), (r K).rest p.2)) ∘ readerParse r K := rfl

lemma measurable_readerStep {γ : Type} [MeasurableSpace γ] (r : StreamReader γ) (K : ℕ) :
    Measurable (fun p : (Fin K → γ) × Streams => (rawWordExtend (p.1, r.read p.2), r.rest p.2)) :=
  ((measurable_rawWordExtend K).comp (measurable_fst.prodMk
    (r.measurable_read.comp measurable_snd))).prodMk (r.measurable_rest.comp measurable_snd)

lemma measurable_readerParse {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ) (K : ℕ) :
    Measurable (readerParse r K) := by
  induction K with
  | zero =>
    have h : readerParse r 0 = fun ω => ((fun q => Fin.elim0 q : Fin 0 → γ), ω) := rfl
    rw [h]
    fun_prop
  | succ K ih =>
    rw [readerParse_succ]
    exact (measurable_readerStep (r K) K).comp ih

/-- The values read sequentially are independent with the readers' laws, and the
unread streams remain IID. -/
theorem readerParse_law {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ) (K : ℕ) :
    iidStreams.map (readerParse r K) =
      (rawWordLaw (fun l => iidStreams.map (r l).read) K).prod iidStreams := by
  have hfinite : ∀ l, IsFiniteMeasure (iidStreams.map (r l).read) := fun _ => inferInstance
  induction K with
  | zero =>
    have h : readerParse r 0 = Prod.mk (fun q => Fin.elim0 q : Fin 0 → γ) := rfl
    rw [h, rawWordLaw, Measure.dirac_prod]
  | succ K ih =>
    let μ := rawWordLaw (fun l => iidStreams.map (r l).read) K
    let : IsFiniteMeasure μ := rawWordLaw_finite _ hfinite K
    have hφ : Measurable (fun ω => ((r K).read ω, (r K).rest ω)) :=
      (r K).measurable_read.prodMk (r K).measurable_rest
    have hsplit : (fun p : (Fin K → γ) × Streams =>
        (rawWordExtend (p.1, (r K).read p.2), (r K).rest p.2)) =
        (Prod.map rawWordExtend id) ∘ (MeasurableEquiv.prodAssoc.symm :
          (Fin K → γ) × (γ × Streams) ≃ᵐ ((Fin K → γ) × γ) × Streams) ∘
          (Prod.map id (fun ω => ((r K).read ω, (r K).rest ω))) := by
      funext p
      rfl
    rw [readerParse_succ, ← Measure.map_map (measurable_readerStep (r K) K)
      (measurable_readerParse r K), ih, hsplit,
      ← Measure.map_map ((measurable_rawWordExtend K).prodMap measurable_id)
        ((MeasurableEquiv.measurable _).comp (measurable_id.prodMap hφ)),
      ← Measure.map_map (MeasurableEquiv.measurable _) (measurable_id.prodMap hφ)]
    have h1 : (μ.prod iidStreams).map (Prod.map id (fun ω => ((r K).read ω, (r K).rest ω))) =
        μ.prod ((iidStreams.map (r K).read).prod iidStreams) := by
      rw [← Measure.map_prod_map _ _ measurable_id hφ, Measure.map_id, (r K).regenerate]
    rw [h1, (measurePreserving_prodAssoc μ (iidStreams.map (r K).read) iidStreams).symm.map_eq,
      ← Measure.map_prod_map _ _ (measurable_rawWordExtend K) measurable_id, Measure.map_id]
    rfl

lemma readerParse_chron {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ) (K : ℕ)
    (ω : Streams) (l : ℕ) (hl : l < K) :
    (readerParse r K ω).1 ⟨K - 1 - l, by omega⟩ = (r l).read (readerParse r l ω).2 := by
  induction K with
  | zero => omega
  | succ K ih =>
    rw [readerParse_succ, Function.comp_apply]
    by_cases hlK : l = K
    · subst hlK
      have hidx : (⟨l + 1 - 1 - l, by omega⟩ : Fin (l + 1)) = 0 := Fin.ext (by simp)
      rw [hidx]
      rfl
    · have hlt : l < K := by omega
      have hidx : (⟨K + 1 - 1 - l, by omega⟩ : Fin (K + 1)) = (⟨K - 1 - l, by omega⟩ : Fin K).succ :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [hidx]
      simp only [rawWordExtend, Fin.cases_succ]
      exact ih hlt

lemma readerParse_congr {γ : Type} [MeasurableSpace γ] (r r' : ℕ → StreamReader γ) (K : ℕ)
    (h : ∀ l, l < K → r l = r' l) : readerParse r K = readerParse r' K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [readerParse_succ, readerParse_succ, ih (fun l hl => h l (by omega)), h K (by omega)]

lemma readerParse_rest_const {γ : Type} [MeasurableSpace γ] (r : ℕ → StreamReader γ)
    (cu cv : ℕ → ℕ) (hu : ∀ l ω, (r l).usedU ω = cu l) (hv : ∀ l ω, (r l).usedV ω = cv l)
    (K : ℕ) (ω : Streams) :
    (readerParse r K ω).2 =
      streamsDrop (∑ l ∈ Finset.range K, cu l) (∑ l ∈ Finset.range K, cv l) ω := by
  induction K with
  | zero => simp [readerParse]
  | succ K ih =>
    rw [readerParse_succ, Function.comp_apply]
    simp only [StreamReader.rest, ih, hu, hv, streamsDrop_drop, Finset.sum_range_succ]

/-- Restricting each sequential input is the same as restricting the product to the
corresponding branch of complete inputs. -/
theorem rawWordLaw_restrict {γ : Type} [MeasurableSpace γ] (μ : ℕ → Measure γ)
    (hμ : ∀ l, IsFiniteMeasure (μ l)) (B : ℕ → Set γ) (hB : ∀ l, MeasurableSet (B l)) (K : ℕ) :
    rawWordLaw (fun l => (μ l).restrict (B l)) K =
      (rawWordLaw μ K).restrict (Set.univ.pi (fun q : Fin K => B (K - 1 - q))) := by
  induction K with
  | zero =>
    have h : (Set.univ.pi (fun q : Fin 0 => B (0 - 1 - q))) = Set.univ := by
      ext p
      simp
    rw [h, Measure.restrict_univ]
    rfl
  | succ K ih =>
    let : IsFiniteMeasure (rawWordLaw μ K) := rawWordLaw_finite μ hμ K
    have hS : MeasurableSet (Set.univ.pi (fun q : Fin (K + 1) => B (K + 1 - 1 - q))) :=
      MeasurableSet.univ_pi (fun q => hB _)
    have hpre : rawWordExtend ⁻¹' (Set.univ.pi (fun q : Fin (K + 1) => B (K + 1 - 1 - q))) =
        (Set.univ.pi (fun q : Fin K => B (K - 1 - q))) ×ˢ B K := by
      ext p
      simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_prod]
      constructor
      · intro h
        refine ⟨fun q => ?_, ?_⟩
        · have hq := h q.succ
          have he : K + 1 - 1 - q.succ.val = K - 1 - q.val := by simp only [Fin.val_succ]; omega
          simpa only [rawWordExtend, Fin.cases_succ, he] using hq
        · have h0 := h 0
          have he : K + 1 - 1 - (0 : Fin (K + 1)).val = K := by simp
          simpa only [rawWordExtend, Fin.cases_zero, he] using h0
      · rintro ⟨h, h0⟩ q
        cases q using Fin.cases with
        | zero =>
          have he : K + 1 - 1 - (0 : Fin (K + 1)).val = K := by simp
          simpa only [rawWordExtend, Fin.cases_zero, he] using h0
        | succ q =>
          have he : K + 1 - 1 - q.succ.val = K - 1 - q.val := by simp only [Fin.val_succ]; omega
          simpa only [rawWordExtend, Fin.cases_succ, he] using h q
    rw [rawWordLaw, rawWordLaw, ih, Measure.restrict_map (measurable_rawWordExtend K) hS, hpre,
      Measure.prod_restrict]

/-- A pushforward splits over an almost-everywhere partition into countably many
measurable pieces. -/
theorem map_eq_sum_restrict_of_partition {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (hd : Pairwise (Function.onFun Disjoint E))
    (hmass : ∑' i, μ (E i) = μ univ) (F : Ω → X) (hF : ∀ i, AEMeasurable F (μ.restrict (E i))) :
    μ.map F = Measure.sum (fun i => (μ.restrict (E i)).map F) := by
  have hunion : μ (⋃ i, E i) = μ univ := by rw [measure_iUnion hd hE, hmass]
  have hcompl : μ (⋃ i, E i)ᶜ = 0 := by
    rw [measure_compl (MeasurableSet.iUnion hE) (measure_ne_top _ _), hunion, tsub_self]
  have hrestrict : μ = Measure.sum (fun i => μ.restrict (E i)) := by
    rw [← Measure.restrict_iUnion hd hE]
    refine (Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr ?_)).symm
    convert hcompl using 2
  have hsum : AEMeasurable F (Measure.sum (fun i => μ.restrict (E i))) :=
    aemeasurable_sum_measure_iff.mpr hF
  conv_lhs => rw [hrestrict]
  exact Measure.map_sum hsum

end JumpProcessesLean.Proofs
