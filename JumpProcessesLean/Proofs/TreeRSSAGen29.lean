import JumpProcessesLean.Proofs.TreeRSSAGen28
import JumpProcessesLean.TreeRSSA.Gen29

/-!
# Generation 29 is generation 28, hence the specification

Generation 29's refresh walks re-add their first levels without testing whether they met the
path of the next changed leaf. Its trees then differ from generation 26's only at strict
ancestors of the pending leaf (`AgreeOff`): a walk writes generation 26's sums up to the meeting
point and, past it, only ancestors of the next leaf (`fixWalkR_agree`), and the last walk of a
refresh writes every ancestor of its leaf, so the trees agree again when the refresh ends
(`fixPathR_agree`, `setBoundsR29_eq`). The driver is generation 26's through these refreshes
(`gen29_run_eq`); the start enters it on trees of depth at least 16 and is otherwise generation
28's (`start29_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

/-! ## Trees that agree off the ancestors of a node -/

/-- `i` is a strict ancestor of node `x`, and not the unused slot `0`. -/
def Above (x i : Nat) : Prop := 0 < i ∧ ∃ j, 0 < j ∧ x / 2 ^ j = i

/-- Trees of one size that agree everywhere except at the strict ancestors of node `x`. -/
def AgreeOff (x : Nat) (t t' : FloatArray) : Prop :=
  t.size = t'.size ∧ ∀ i, i < t.size → ¬ Above x i → t.get! i = t'.get! i

theorem div_two_pow_succ (x j : Nat) : x / 2 ^ (j + 1) = x / 2 / 2 ^ j := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem two_le_two_pow {j : Nat} (hj : 0 < j) : 2 ≤ 2 ^ j := by
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj

theorem above_iff (x i : Nat) : Above x i ↔ (0 < i ∧ i = x / 2) ∨ Above (x / 2) i := by
  constructor
  · rintro ⟨hi, j, hj, h⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [div_two_pow_succ] at h
    rcases Nat.eq_zero_or_pos j' with h0 | h0
    · subst h0
      left
      simp only [Nat.pow_zero, Nat.div_one] at h
      exact ⟨hi, h.symm⟩
    · exact Or.inr ⟨hi, j', h0, h⟩
  · rintro (⟨hi, h⟩ | ⟨hi, j, hj, h⟩)
    · exact ⟨hi, 1, by omega, by rw [h]; rfl⟩
    · exact ⟨hi, j + 1, by omega, by rw [div_two_pow_succ]; exact h⟩

theorem not_above_self (x : Nat) : ¬ Above x x := by
  rintro ⟨hx, j, hj, h⟩
  have : x / 2 ^ j < x := Nat.div_lt_self hx (by have := two_le_two_pow hj; omega)
  omega

theorem div_two_pow_le_half (x j : Nat) (hj : 0 < j) : x / 2 ^ j ≤ x / 2 := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [div_two_pow_succ]
  exact Nat.div_le_self _ _

/-- A node's sibling is not among its strict ancestors. -/
theorem not_above_sib (x : Nat) : ¬ Above x (2 * (x / 2) + (1 - x % 2)) := by
  rintro ⟨hi, j, hj, h⟩
  have h1 := div_two_pow_le_half x j hj
  generalize x / 2 ^ j = y at h h1
  omega

theorem not_above_one (i : Nat) : ¬ Above 1 i := by
  rintro ⟨hi, j, hj, h⟩
  have : 1 / 2 ^ j = 0 := Nat.div_eq_of_lt (by have := two_le_two_pow hj; omega)
  omega

/-- Past the meeting point of the walks from `x` and from `ℓ`, the ancestors of `x` are
ancestors of `ℓ`. -/
theorem above_of_meet {x y ℓ s : Nat} (hxy : x / 2 = y / 2) (hy : y = ℓ / 2 ^ s) :
    ∀ i, Above x i → Above ℓ i := by
  intro i hx
  have e : x / 2 = ℓ / 2 ^ (s + 1) := by
    rw [hxy, hy, Nat.div_div_eq_div_mul, Nat.pow_succ]
  rcases (above_iff x i).mp hx with ⟨hi, h⟩ | ⟨hi, j, hj, h⟩
  · exact ⟨hi, s + 1, by omega, by rw [h, e]⟩
  · refine ⟨hi, s + 1 + j, by omega, ?_⟩
    rw [e, Nat.div_div_eq_div_mul, ← Nat.pow_add] at h
    exact h

theorem agreeOff_mono {x y : Nat} {t t' : FloatArray} (hxy : ∀ i, Above x i → Above y i)
    (h : AgreeOff x t t') : AgreeOff y t t' :=
  ⟨h.1, fun i hi hy => h.2 i hi (fun hx => hy (hxy i hx))⟩

theorem agreeOff_refl (x : Nat) (t : FloatArray) : AgreeOff x t t :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-- Writing one sum at the parent of `x` in both trees. -/
theorem agreeOff_set (x : Nat) (t t' : FloatArray) (h : AgreeOff x t t') (v : Float)
    (hk : x / 2 < t.size) : AgreeOff (x / 2) (t.set! (x / 2) v) (t'.set! (x / 2) v) := by
  refine ⟨by rw [fa_size_set!, fa_size_set!, h.1], fun i hi ha => ?_⟩
  rw [fa_size_set!] at hi
  by_cases e : i = x / 2
  · subst e
    rw [fa_get!_set!_self _ _ _ hk, fa_get!_set!_self _ _ _ (by rw [← h.1]; exact hk)]
  · rw [fa_get!_set!_ne _ _ _ _ (fun h' => e h'.symm),
      fa_get!_set!_ne _ _ _ _ (fun h' => e h'.symm)]
    refine h.2 i hi (fun hx => ?_)
    rcases (above_iff x i).mp hx with ⟨_, h'⟩ | h'
    · exact e h'
    · exact ha h'

/-- Writing one value at node `x` itself in both trees. -/
theorem agreeOff_set_self (x : Nat) (t t' : FloatArray) (h : AgreeOff x t t') (v : Float)
    (hk : x < t.size) : AgreeOff x (t.set! x v) (t'.set! x v) := by
  refine ⟨by rw [fa_size_set!, fa_size_set!, h.1], fun i hi ha => ?_⟩
  rw [fa_size_set!] at hi
  by_cases e : i = x
  · subst e
    rw [fa_get!_set!_self _ _ _ hk, fa_get!_set!_self _ _ _ (by rw [← h.1]; exact hk)]
  · rw [fa_get!_set!_ne _ _ _ _ (fun h' => e h'.symm),
      fa_get!_set!_ne _ _ _ _ (fun h' => e h'.symm)]
    exact h.2 i hi ha

theorem floatArray_eq_of_get (t t' : FloatArray) (hs : t.size = t'.size)
    (h : ∀ i, i < t.size → t.get! i = t'.get! i) : t = t' := by
  cases t with
  | mk d =>
    cases t' with
    | mk d' =>
      congr 1
      apply Array.ext hs
      intro i h1 h2
      have := h i h1
      simp only [FloatArray.get!, getElem!_pos d i h1, getElem!_pos d' i h2] at this
      exact this

/-! ## Copies of generation 26's walks -/

theorem fixUntilR29_eq (P : USize) : ∀ (m : Nat) (n : USize), n.toNat = m →
    ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float),
      Gen29.fixUntilR P n tree hP node hn other v =
        Gen26.fixUntilR P n tree hP node hn other v := by
  intro m
  induction m with
  | zero =>
    intro n hm tree hP node hn other v
    have hz : n = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [Gen29.fixUntilR, dite_eq_left hz, Gen26.fixUntilR, dite_eq_left hz]
  | succ m ih =>
    intro n hm tree hP node hn other v
    have hz : n ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [Gen29.fixUntilR, dite_eq_right hz, Gen26.fixUntilR, dite_eq_right hz]
    simp only [ih (n - 1) (by rw [Gen16.pred_toNat n hz]; omega)]

theorem fixPathR29_eq (P : USize) : ∀ (m : Nat) (n : USize), n.toNat = m →
    ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (v : Float),
      Gen29.fixPathR P n tree hP node hn v = Gen26.fixPathR P n tree hP node hn v := by
  intro m
  induction m with
  | zero =>
    intro n hm tree hP node hn v
    have hz : n = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [Gen29.fixPathR, dite_eq_left hz, Gen26.fixPathR, dite_eq_left hz]
  | succ m ih =>
    intro n hm tree hP node hn v
    have hz : n ≠ 0 := fun h => by rw [h] at hm; simp at hm
    rw [Gen29.fixPathR, dite_eq_right hz, Gen26.fixPathR, dite_eq_right hz]
    simp only [ih (n - 1) (by rw [Gen16.pred_toNat n hz]; omega)]

/-! ## The walks on indices -/

/-- `Gen29.fixWalkR` on indices: `w` levels re-added without the meeting test, then
`Gen3.fixUntil` with the remaining levels. -/
def walkFixed (tree : FloatArray) : Nat → Nat → Nat → Nat → FloatArray
  | 0, n, node, other => Gen3.fixUntil tree n node other
  | w + 1, n, node, other =>
    let k := node / 2
    walkFixed (tree.set! k (tree.get! (2 * k) + tree.get! (2 * k + 1))) w (n - 1) k (other / 2)

theorem fixUntilR_nat (P : USize) (n : USize) (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size)
    (node : USize) (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float)
    (hv : tree.get! node.toNat = v) :
    Gen26.fixUntilR P n tree hP node hn other v =
      Gen3.fixUntil tree n.toNat node.toNat other.toNat := by
  rw [fixUntilR26_eq P _ n rfl, fixUntilGo16_eq P _ n rfl, fixUntilGo_eq P _ _ _ _ _ _ _ hv]

theorem fixPathR_nat (P : USize) (n : USize) (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size)
    (node : USize) (hn : node.toNat < 2 * P.toNat) (v : Float) (hv : tree.get! node.toNat = v) :
    Gen26.fixPathR P n tree hP node hn v = Gen1.fixPath tree n.toNat node.toNat := by
  rw [fixPathR26_eq P _ n rfl, fixPathGo16_eq P _ n rfl, fixPathGo_eq P _ _ _ _ _ _ hv]

theorem fixWalkR_nat (P : USize) : ∀ (m : Nat) (n w : USize) (hw : w.toNat ≤ n.toNat),
    w.toNat = m → ∀ (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size) (node : USize)
      (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float),
      tree.get! node.toNat = v →
      Gen29.fixWalkR P n w hw tree hP node hn other v =
        walkFixed tree m n.toNat node.toNat other.toNat := by
  intro m
  induction m with
  | zero =>
    intro n w hw hm tree hP node hn other v hv
    have hz : w = 0 := USize.toNat_inj.mp (by rw [hm]; rfl)
    rw [Gen29.fixWalkR, dite_eq_left hz, fixUntilR29_eq P _ n rfl, fixUntilR_nat P n tree hP
      node hn other v hv]
    rfl
  | succ m ih =>
    intro n w hw hm tree hP node hn other v hv
    have hz : w ≠ 0 := fun h => by rw [h] at hm; simp at hm
    have hn0 : n ≠ 0 := fun h => by rw [h] at hw; simp at hw; omega
    rw [Gen29.fixWalkR, dite_eq_right hz, walkFixed]
    dsimp only
    have hk : (node >>> 1).toNat = node.toNat / 2 := Gen12.shiftRight_one_toNat node
    have ho : (other >>> 1).toNat = other.toNat / 2 := Gen12.shiftRight_one_toNat other
    rw [ih (n - 1) (w - 1) _ (by rw [Gen16.pred_toNat w hz]; omega)]
    · rw [floatArray_uset_eq, floatArray_uget_eq, sibling_sum tree node v hv, hk, ho,
        Gen16.pred_toNat n hn0]
    · rw [floatArray_uset_eq, hk]
      apply floatArray_get!_set!_self
      omega

theorem fixUntil_size : ∀ (n : Nat) (tree : FloatArray) (node other : Nat),
    (Gen3.fixUntil tree n node other).size = tree.size := by
  intro n
  induction n with
  | zero => intro tree node other; rfl
  | succ n ih =>
    intro tree node other
    simp only [Gen3.fixUntil]
    split
    · rfl
    · rw [ih, fa_size_set!]

theorem walkFixed_size : ∀ (w n : Nat) (tree : FloatArray) (node other : Nat),
    (walkFixed tree w n node other).size = tree.size := by
  intro w
  induction w with
  | zero => intro n tree node other; exact fixUntil_size n tree node other
  | succ w ih =>
    intro n tree node other
    simp only [walkFixed]
    rw [ih, fa_size_set!]

/-! ## Walks on trees that agree off the ancestors of the walk's node -/

/-- Neither child of a node's parent is a strict ancestor of the node. -/
theorem not_above_child (x c : Nat) (hc : c ≤ 1) : ¬ Above x (2 * (x / 2) + c) := by
  rintro ⟨hi, j, hj, h⟩
  have h1 := div_two_pow_le_half x j hj
  generalize x / 2 ^ j = y at h h1
  omega

/-- One step of a walk in both trees: the children of `x / 2` agree, so its sum does. -/
theorem agreeOff_walk_step (x : Nat) (t1 t2 : FloatArray) (h : AgreeOff x t1 t2)
    (hs : 2 * (x / 2) + 1 < t1.size) :
    AgreeOff (x / 2) (t1.set! (x / 2) (t1.get! (2 * (x / 2)) + t1.get! (2 * (x / 2) + 1)))
      (t2.set! (x / 2) (t2.get! (2 * (x / 2)) + t2.get! (2 * (x / 2) + 1))) := by
  have e1 : t1.get! (2 * (x / 2)) = t2.get! (2 * (x / 2)) := by
    have := h.2 (2 * (x / 2) + 0) (by omega) (not_above_child x 0 (by omega))
    simpa using this
  have e2 : t1.get! (2 * (x / 2) + 1) = t2.get! (2 * (x / 2) + 1) :=
    h.2 _ (by omega) (not_above_child x 1 (by omega))
  rw [e1, e2]
  exact agreeOff_set x t1 t2 h _ (by omega)

theorem level_half {m x : Nat} (hlo : 2 ^ (m + 1) ≤ x) (hhi : x < 2 ^ (m + 1 + 1)) :
    2 ^ m ≤ x / 2 ∧ x / 2 < 2 ^ (m + 1) := by
  have e1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
  have e2 : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  omega

theorem pos_div_two_pow {x j n : Nat} (h : 2 ^ n ≤ x) (hj : j ≤ n) : 0 < x / 2 ^ j :=
  Nat.div_pos (Nat.le_trans (Nat.pow_le_pow_right (by omega) hj) h) (Nat.two_pow_pos j)

/-- The final walk of a refresh writes every strict ancestor of its node, so trees that agree
off them become equal. -/
theorem fixPath_agree : ∀ (n x : Nat) (t1 t2 : FloatArray), 2 ^ n ≤ x → x < 2 ^ (n + 1) →
    2 * (x / 2) + 1 < t1.size → AgreeOff x t1 t2 → Gen1.fixPath t1 n x = Gen1.fixPath t2 n x := by
  intro n
  induction n with
  | zero =>
    intro x t1 t2 hlo hhi _ ha
    have e : x = 1 := by simp at hlo hhi; omega
    subst e
    rw [floatArray_eq_of_get t1 t2 ha.1 (fun i hi => ha.2 i hi (not_above_one i))]
  | succ n ih =>
    intro x t1 t2 hlo hhi hs ha
    simp only [Gen1.fixPath]
    have hl := level_half hlo hhi
    exact ih (x / 2) _ _ hl.1 hl.2 (by rw [fa_size_set!]; omega) (agreeOff_walk_step x t1 t2 ha hs)

/-- Generation 26's walk in both trees: they then agree off the strict ancestors of `ℓ`, whose
ancestor `o` the walk climbs towards. -/
theorem fixUntil_agree (ℓ : Nat) : ∀ (n x o : Nat) (t1 t2 : FloatArray), 2 ^ n ≤ x →
    x < 2 ^ (n + 1) → 2 * (x / 2) + 1 < t1.size → (∃ s, o = ℓ / 2 ^ s) → AgreeOff x t1 t2 →
    AgreeOff ℓ (Gen3.fixUntil t1 n x o) (Gen3.fixUntil t2 n x o) := by
  intro n
  induction n with
  | zero =>
    intro x o t1 t2 hlo hhi _ _ ha
    have e : x = 1 := by simp at hlo hhi; omega
    subst e
    exact agreeOff_mono (fun i h => absurd h (not_above_one i)) ha
  | succ n ih =>
    intro x o t1 t2 hlo hhi hs ⟨s, ho⟩ ha
    simp only [Gen3.fixUntil]
    by_cases hko : x / 2 = o / 2
    · rw [ite_eq_left hko, ite_eq_left hko]
      exact agreeOff_mono (above_of_meet hko ho) ha
    · rw [ite_eq_right hko, ite_eq_right hko]
      have hl := level_half hlo hhi
      exact ih (x / 2) (o / 2) _ _ hl.1 hl.2 (by rw [fa_size_set!]; omega)
        ⟨s + 1, by rw [ho, Nat.div_div_eq_div_mul, Nat.pow_succ]⟩ (agreeOff_walk_step x t1 t2 ha hs)

/-- A fixed walk from a node that already met the other path writes only the node's first `w`
ancestors. -/
theorem walkFixed_met : ∀ (w n x : Nat) (t : FloatArray) (i : Nat),
    (∀ j, 0 < j → j ≤ w → x / 2 ^ j ≠ i) → (walkFixed t w n x x).get! i = t.get! i := by
  intro w
  induction w with
  | zero =>
    intro n x t i _
    simp only [walkFixed]
    cases n with
    | zero => rfl
    | succ n => simp only [Gen3.fixUntil, ite_true]
  | succ w ih =>
    intro n x t i hi
    simp only [walkFixed]
    rw [ih (n - 1) (x / 2) _ i (fun j hj hjw => by
      rw [← div_two_pow_succ]; exact hi (j + 1) (by omega) (by omega))]
    have h1 := hi 1 (by omega) (by omega)
    simp only [Nat.pow_one] at h1
    exact fa_get!_set!_ne _ _ _ _ h1

/-- Generation 29's walk against generation 26's: the trees then agree off the strict
ancestors of `ℓ`, whose ancestor `o` both walks climb towards. -/
theorem walkFixed_agree (ℓ : Nat) : ∀ (w n x o : Nat) (t1 t2 : FloatArray), w ≤ n →
    2 ^ n ≤ x → x < 2 ^ (n + 1) → 2 * (x / 2) + 1 < t1.size → (∃ s, o = ℓ / 2 ^ s) →
    AgreeOff x t1 t2 → AgreeOff ℓ (walkFixed t1 w n x o) (Gen3.fixUntil t2 n x o) := by
  intro w
  induction w with
  | zero =>
    intro n x o t1 t2 _ hlo hhi hs ho ha
    exact fixUntil_agree ℓ n x o t1 t2 hlo hhi hs ho ha
  | succ w ih =>
    intro n x o t1 t2 hw hlo hhi hs ⟨s, ho⟩ ha
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [walkFixed, Gen3.fixUntil, Nat.add_sub_cancel]
    have hl := level_half hlo hhi
    by_cases hko : x / 2 = o / 2
    · -- generation 26's walk stops; generation 29's goes on along ancestors of `ℓ`
      rw [ite_eq_left hko, ← hko]
      have hsub := above_of_meet hko ho
      refine ⟨by rw [walkFixed_size, fa_size_set!, ha.1], fun i hi hA => ?_⟩
      rw [walkFixed_size, fa_size_set!] at hi
      rw [walkFixed_met w n' (x / 2) _ i (fun j hj hjw he => hA (by
        rw [← he, ← div_two_pow_succ]
        exact hsub _ ⟨pos_div_two_pow hlo (by omega), j + 1, by omega, rfl⟩))]
      rw [fa_get!_set!_ne _ _ _ _ (fun he => hA (by
        rw [← he]
        exact hsub _ ⟨by omega, 1, by omega, by simp⟩))]
      exact ha.2 i hi (fun hx => hA (hsub i hx))
    · rw [ite_eq_right hko]
      exact ih n' (x / 2) (o / 2) _ _ (by omega) hl.1 hl.2 (by rw [fa_size_set!]; omega)
        ⟨s + 1, by rw [ho, Nat.div_div_eq_div_mul, Nat.pow_succ]⟩ (agreeOff_walk_step x t1 t2 ha hs)

/-! ## Refreshes -/

theorem setBoundsR29_eq (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (hD : 11 ≤ D.toNat) (hPD : P.toNat = 2 ^ D.toNat) (nW : USize) (hi : FloatArray)
    (hhi : nW.toNat ≤ hi.size) (h0 h1 g0 g1 : Float) (ds : Array Gen18.DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat) :
    ∀ m (i : USize), ds.size - i.toNat = m → ∀ (t1 t2 : FloatArray)
      (ht1 : 2 * P.toNat ≤ t1.size) (ht2 : 2 * P.toNat ≤ t2.size) (pending : USize) hpend,
      (pending = 0 → t1 = t2) →
      (pending ≠ 0 → AgreeOff pending.toNat t1 t2 ∧ P.toNat ≤ pending.toNat) →
      Gen29.setBoundsR P hP2 D hD nW hi hhi h0 h1 g0 g1 ds hds i t1 ht1 pending hpend =
        Gen26.setBoundsR P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i t2 ht2 pending hpend := by
  have hlev : ∀ x : USize, P.toNat ≤ x.toNat → x.toNat < 2 * P.toNat →
      2 ^ D.toNat ≤ x.toNat ∧ x.toNat < 2 ^ (D.toNat + 1) := by
    intro x h1 h2
    rw [Nat.pow_succ, ← hPD]
    omega
  -- the last walk of a refresh makes the trees equal
  have hlast : ∀ (t1 t2 : FloatArray) (ht1 : 2 * P.toNat ≤ t1.size)
      (ht2 : 2 * P.toNat ≤ t2.size) (pending : USize) (hp : pending.toNat < 2 * P.toNat),
      AgreeOff pending.toNat t1 t2 → P.toNat ≤ pending.toNat →
      Gen29.fixPathR P D t1 ht1 pending hp (t1.uget pending (by omega)) =
        Gen26.fixPathR P D t2 ht2 pending hp (t2.uget pending (by omega)) := by
    intro t1 t2 ht1 ht2 pending hp ha hP
    rw [fixPathR29_eq P _ D rfl,
      fixPathR_nat P D t1 ht1 pending hp _ (floatArray_uget_eq _ _ _).symm,
      fixPathR_nat P D t2 ht2 pending hp _ (floatArray_uget_eq _ _ _).symm]
    exact fixPath_agree _ _ t1 t2 (hlev _ hP hp).1 (hlev _ hP hp).2 (by omega) ha
  intro m
  induction m with
  | zero =>
    intro i hm t1 t2 ht1 ht2 pending hpend he ha
    have hge : ¬ i < ds.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize ds i h; omega
    rw [Gen29.setBoundsR, dite_eq_right hge, Gen26.setBoundsR, dite_eq_right hge]
    by_cases hz : pending = 0
    · rw [dite_eq_left hz, dite_eq_left hz]; exact he hz
    · rw [dite_eq_right hz, dite_eq_right hz]
      exact hlast t1 t2 ht1 ht2 pending _ (ha hz).1 (ha hz).2
  | succ m ih =>
    intro i hm t1 t2 ht1 ht2 pending hpend he ha
    by_cases h : i < ds.usize
    · have hs := Gen15.succ_toNat_of_lt_usize ds i h
      have hi' := Gen15.lt_size_of_lt_usize ds i h
      have hk : (ds.uget i hi').k.toNat < P.toNat := (hds i.toNat hi').1
      have hleaf : (P + (ds.uget i hi').k).toNat = P.toNat + (ds.uget i hi').k.toNat := by
        have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
        rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [Gen29.setBoundsR, dite_eq_left h, Gen26.setBoundsR, dite_eq_left h]
      dsimp only
      refine ite_congr rfl (fun _ => ih (i + 1) (by omega) _ _ _ _ _ _ he ha)
        (fun _ => ite_congr rfl (fun _ => ih (i + 1) (by omega) _ _ _ _ _ _ he ha) (fun _ => ?_))
      apply ih (i + 1) (by omega)
      · intro hz
        exfalso
        have : (P + (ds.uget i hi').k).toNat = 0 := by rw [hz]; rfl
        have hP0 : 0 < P.toNat := by rw [hPD]; exact Nat.two_pow_pos _
        omega
      · intro _
        refine ⟨?_, by rw [hleaf]; omega⟩
        rw [floatArray_uset_eq, floatArray_uset_eq]
        refine agreeOff_set_self _ _ _ ?_ _ ?_
        · by_cases hz : pending = 0
          · rw [dite_eq_left hz, dite_eq_left hz, he hz]
            exact agreeOff_refl _ _
          · rw [dite_eq_right hz, dite_eq_right hz]
            obtain ⟨ha', hP⟩ := ha hz
            have hp := hpend.resolve_left hz
            rw [fixWalkR_nat P _ D _ _ rfl t1 ht1 pending hp _ _ (floatArray_uget_eq _ _ _).symm,
              fixUntilR_nat P D t2 ht2 pending hp _ _ (floatArray_uget_eq _ _ _).symm]
            exact walkFixed_agree _ _ _ _ _ t1 t2
              (by rw [Gen29.usizeLit_toNat 11 (by omega)]; exact hD) (hlev _ hP hp).1
              (hlev _ hP hp).2 (by omega) ⟨0, by simp⟩ ha'
        · split
          · rw [hleaf]; omega
          · rw [Gen29.fixWalkR_size P _ D _ _ rfl, hleaf]; omega
    · rw [Gen29.setBoundsR, dite_eq_right h, Gen26.setBoundsR, dite_eq_right h]
      by_cases hz : pending = 0
      · rw [dite_eq_left hz, dite_eq_left hz]; exact he hz
      · rw [dite_eq_right hz, dite_eq_right hz]
        exact hlast t1 t2 ht1 ht2 pending _ (ha hz).1 (ha hz).2

theorem rebracketR29_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (hD : 11 ≤ D.toNat) (hPD : P.toNat = 2 ^ D.toNat) (nW numRx : USize)
    (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) (s : USize)
    (hs : s.toNat < nW.toNat) :
    Gen29.rebracketR W P hP2 D hD nW numRx rates hB pop hpop c hc s hs =
      Gen26.rebracketR W P hP2 D nW numRx rates hB pop hpop c hc s hs := by
  simp only [Gen29.rebracketR, Gen26.rebracketR]
  congr 1
  exact setBoundsR29_eq P hP2 D hD hPD _ _ _ _ _ _ _ _ _ _ 0 rfl _ _ _ _ 0 _ (fun _ => rfl)
    (fun h => absurd rfl h)

theorem refresh1_29_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (hD : 11 ≤ D.toNat) (hPD : P.toNat = 2 ^ D.toNat) (nW numRx : USize)
    (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (s : USize) (hs : s.toNat < nW.toNat) (c : Gen19.CacheV)
    (hc : Gen20.Sized nW P c) :
    Gen29.refresh1 W P hP2 D hD nW numRx rates hB pop hpop s hs c hc =
      Gen26.refresh1 W P hP2 D nW numRx rates hB pop hpop s hs c hc := by
  simp only [Gen29.refresh1, Gen26.refresh1, rebracketR29_eq W P hP2 D hD hPD]

theorem refreshFromRV29_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (hD : 11 ≤ D.toNat) (hPD : P.toNat = 2 ^ D.toNat) (nW numRx : USize)
    (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates) (r : Gen26.RxV)
    (h0 : r.c0.toNat < nW.toNat) (h1 : r.one = false → r.c1.toNat < nW.toNat)
    (h2 : r.three = true → r.c2.toNat < nW.toNat) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (c : Gen19.CacheV) (hc : Gen20.Sized nW P c) :
    Gen29.refreshFromRV W P hP2 D hD nW numRx rates hB r h0 h1 h2 pop hpop c hc =
      Gen26.refreshFromRV W P hP2 D nW numRx rates hB r h0 h1 h2 pop hpop c hc := by
  simp only [Gen29.refreshFromRV, Gen26.refreshFromRV, refresh1_29_eq W P hP2 D hD hPD]

/-! ## The driver -/

theorem level_one_pow {P D : USize} (hL : Gen22.Level P D 1) : P.toNat = 2 ^ D.toNat := by
  obtain ⟨i, n, hP, hid, h1, h2⟩ := hL
  have e1 : (1 : USize).toNat = 1 := by
    rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
  rw [e1] at h1 h2
  have hi : i = 0 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact h
    · have := two_le_two_pow h; omega
  subst hi
  rw [hP]; congr 1; omega

theorem run29_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (hD : 11 ≤ D.toNat)
    (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates) (hL : Gen22.Level P D 1)
    (rxs : Array Gen26.RxV) (hR : Gen26.RxOKV W rates numRx.toNat rxs) (horizon : Float)
    (save : Bool) (cap : USize) (fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = f →
      Gen29.run C codes W msN n hms hval nW numRx P hP2 D hD rates hB hL rxs hR horizon save cap
          evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen26.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
      evW.toNat = fuel → prW.toNat = prFuel →
      Gen29.run C codes W msN n hms hval nW numRx P hP2 D hD rates hB hL rxs hR horizon save cap
          evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen26.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace := by
  have hPD := level_one_pow hL
  intro prFuel
  induction prFuel with
  | zero =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have h0 : prW = 0 := USize.toNat_inj.mp (by rw [hpr]; rfl)
    rw [Gen29.run, dite_eq_left h0, Gen26.run, dite_eq_left h0]
  | succ pf ih =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have ih' : ∀ pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
        Gen29.run C codes W msN n hms hval nW numRx P hP2 D hD rates hB hL rxs hR horizon save cap
            evW (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
          Gen26.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap
            evW (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace :=
      fun pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
        ih evW (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
          (usize_pred_toNat hpr)
    by_cases he : evW = 0
    · rw [Gen29.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen26.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr)]
      simp only [dite_eq_left he, Gen29.descend2_eq26, Gen29.descendW_eq26, ih']
    · obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
        have : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
        omega⟩
      have hn' : ∀ (prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize)
          trace,
          Gen29.run C codes W msN n hms hval nW numRx P hP2 D hD rates hB hL rxs hR horizon save
              cap (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
            Gen26.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save
              cap (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace :=
        fun prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
          hnext f hf (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace
            (by rw [Gen16.pred_toNat evW he]; omega)
      rw [Gen29.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen26.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr)]
      simp only [dite_eq_right he, Gen29.descend2_eq26, Gen29.descendW_eq26, ih', hn',
        refreshFromRV29_eq W P hP2 D hD hPD]

/-- Generation 29's driver returns what generation 26's returns. -/
theorem gen29_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (hD : 11 ≤ D.toNat)
    (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates) (hL : Gen22.Level P D 1)
    (rxs : Array Gen26.RxV) (hR : Gen26.RxOKV W rates numRx.toNat rxs) (horizon : Float)
    (save : Bool) (cap : USize) :
    ∀ fuel prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize)
      trace, evW.toNat = fuel → prW.toNat = prFuel →
      Gen29.run C codes W msN n hms hval nW numRx P hP2 D hD rates hB hL rxs hR horizon save cap
          evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen26.run C codes W msN n hms hval nW numRx P hP2 D rates hB hL rxs hR horizon save cap evW
          prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run29_eq_of C codes W msN n hms hval nW numRx P hP2 D hD rates hB hL rxs hR horizon save
      cap 0 (fun f h => absurd h (by omega))
  | succ f ih =>
    refine run29_eq_of C codes W msN n hms hval nW numRx P hP2 D hD rates hB hL rxs hR horizon save
      cap (f + 1) ?_
    intro f' hf' evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
    obtain rfl : f' = f := by omega
    exact ih prW.toNat evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev rfl

/-- Generation 29's start is generation 28's. -/
theorem start29_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (count : Nat) (trace : Array (Float × State)) :
    Gen29.start C codes horizon save cap fuel pop c now rng count trace =
      Gen28.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen29.start Gen28.start
  dsimp only
  split
  · split
    · exact gen29_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ rfl rfl
    · rfl
  · rfl

/-- Generation 29 returns what generation 28 returns, on every network and input. -/
theorem gen29_eq_gen28 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen29.simulate net initial start horizon rng maxEvents save cap =
      Gen28.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen29.simulate Gen28.simulate
  simp only [start29_eq]

/-- **Generation 29 is the specification.** For every network whose reactant species are in
range and every input, generation 29 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen29_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen29.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen29_eq_gen28, gen28_simulate_eq net hwf]

end JumpProcessesLean.Proofs
