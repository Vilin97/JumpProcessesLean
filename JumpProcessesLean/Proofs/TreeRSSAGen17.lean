import JumpProcessesLean.Proofs.TreeRSSAGen16
import JumpProcessesLean.TreeRSSA.Gen17

/-!
# Generation 17 is generation 16, hence the specification

The dropped range tests are implied by the kept ones in Lean's model of `Float`: `0 ≤ u` gives
`-∞ < u`, `u < 1` gives `u < ∞`, `0 < e` gives `-∞ < e`, and `now < t` gives both `-∞ < t` and
`now ≤ t`; every test of a group raises the same error (`uniform_checks`, `exponential_checks`,
`time_checks`). The machine-word reads are `get!` (`fget_eq`, `aget_eq`, `changesAt_val`) and the
descent ends at a leaf (`descendW17_eq`, `descendW17_ge`).

Firing: if no species is outside its bracket, a species that only gained can be stale only above
`hi`, and one that only lost only below `lo` or the maximal stoichiometry (`staleI_up`,
`staleI_down`). With distinct species per reaction, the one loop applies the changes of generation
15's fold and appends an entry exactly when one of the changed species ends outside its bracket
(`applyTest_eq`); then it is generation 13's firing (`fire17`). A refresh puts its species inside
the bracket of its own count and changes no other bracket (`staleI_bracket`,
`foldRefresh13_brackets`), so no species is outside its bracket after an event either, and the
total, the tree's root, is unchanged when no refresh ran. With these invariants (`RunInv`) the
driver is generation 16's (`run17_eq_of`, `gen17_run_eq`); the start tests the network's changes,
the initial brackets and the word sizes, and otherwise runs generation 16 (`start17_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)
open JumpProcessesLean.TreeRSSA.Gen7 (floatInf floatNegInf)

/-! ## Order facts in Lean's model of `Float` -/

section Order
open Float.Model

theorem decide_float_le (a b : Float) :
    decide (a ≤ b) = a.toModel.unpack.le b.toModel.unpack := by
  show decide (Float.le a b = true) = _
  rw [Bool.decide_eq_true]
  unfold Float.le
  show decide (a.toModel.le b.toModel = true) = _
  rw [Bool.decide_eq_true]
  rfl

lemma unpacked_lt_left {a b : UnpackedFloat} (h : a.lt b = true) :
    a ≠ .notANumber ∧ a ≠ .infinity .positive := by
  cases a with
  | notANumber => simp [UnpackedFloat.lt, UnpackedFloat.compare] at h
  | infinity s =>
    cases s with
    | negative => exact ⟨by simp, by simp⟩
    | positive =>
      cases b with
      | notANumber => simp [UnpackedFloat.lt, UnpackedFloat.compare] at h
      | infinity t => cases t <;> simp [UnpackedFloat.lt, UnpackedFloat.compare, compare] at h
      | zero t => simp [UnpackedFloat.lt, UnpackedFloat.compare] at h
      | finite t m e hm => simp [UnpackedFloat.lt, UnpackedFloat.compare] at h
  | zero s => exact ⟨by simp, by simp⟩
  | finite s m e hm => exact ⟨by simp, by simp⟩

lemma unpacked_lt_right {a b : UnpackedFloat} (h : a.lt b = true) :
    b ≠ .notANumber ∧ b ≠ .infinity .negative := by
  cases b with
  | notANumber => cases a <;> simp [UnpackedFloat.lt, UnpackedFloat.compare] at h
  | infinity t =>
    cases t with
    | positive => exact ⟨by simp, by simp⟩
    | negative =>
      cases a with
      | notANumber => simp [UnpackedFloat.lt, UnpackedFloat.compare] at h
      | infinity s => cases s <;> simp [UnpackedFloat.lt, UnpackedFloat.compare, compare] at h
      | zero s => simp [UnpackedFloat.lt, UnpackedFloat.compare] at h
      | finite s m e hm => cases s <;> simp [UnpackedFloat.lt, UnpackedFloat.compare] at h
  | zero t => exact ⟨by simp, by simp⟩
  | finite t m e hm => exact ⟨by simp, by simp⟩

lemma unpacked_lt_inf {a : UnpackedFloat} (h1 : a ≠ .notANumber) (h2 : a ≠ .infinity .positive) :
    a.lt (.infinity .positive) = true := by
  cases a with
  | notANumber => exact absurd rfl h1
  | infinity s =>
    cases s with
    | positive => exact absurd rfl h2
    | negative => simp [UnpackedFloat.lt, UnpackedFloat.compare, compare]
  | zero s => simp [UnpackedFloat.lt, UnpackedFloat.compare]
  | finite s m e hm => cases s <;> simp [UnpackedFloat.lt, UnpackedFloat.compare]

lemma unpacked_negInf_lt {b : UnpackedFloat} (h1 : b ≠ .notANumber)
    (h2 : b ≠ .infinity .negative) : (UnpackedFloat.infinity .negative).lt b = true := by
  cases b with
  | notANumber => exact absurd rfl h1
  | infinity t =>
    cases t with
    | negative => exact absurd rfl h2
    | positive => simp [UnpackedFloat.lt, UnpackedFloat.compare, compare]
  | zero t => simp [UnpackedFloat.lt, UnpackedFloat.compare]
  | finite t m e hm => simp [UnpackedFloat.lt, UnpackedFloat.compare]

lemma unpacked_le_of_lt {a b : UnpackedFloat} (h : a.lt b = true) : a.le b = true := by
  simp only [UnpackedFloat.lt, beq_iff_eq] at h
  simp [UnpackedFloat.le, h]

lemma unpacked_le_right {a b : UnpackedFloat} (h : a.le b = true)
    (ha : a ≠ .infinity .negative) : b ≠ .notANumber ∧ b ≠ .infinity .negative := by
  cases b with
  | notANumber => cases a <;> simp [UnpackedFloat.le, UnpackedFloat.compare] at h
  | infinity t =>
    cases t with
    | positive => exact ⟨by simp, by simp⟩
    | negative =>
      cases a with
      | notANumber => simp [UnpackedFloat.le, UnpackedFloat.compare] at h
      | infinity s =>
        cases s with
        | negative => exact absurd rfl ha
        | positive => simp [UnpackedFloat.le, UnpackedFloat.compare, compare] at h
      | zero s => simp [UnpackedFloat.le, UnpackedFloat.compare] at h
      | finite s m e hm => cases s <;> simp [UnpackedFloat.le, UnpackedFloat.compare] at h
  | zero t => exact ⟨by simp, by simp⟩
  | finite t m e hm => exact ⟨by simp, by simp⟩

theorem floatZero_unpack : floatZero.toModel.unpack = .zero .positive := by rfl

theorem float_le_of_lt {a b : Float} (h : decide (a < b) = true) : decide (a ≤ b) = true := by
  rw [decide_float_lt] at h; rw [decide_float_le]; exact unpacked_le_of_lt h

theorem float_lt_inf_of_lt {a b : Float} (h : decide (a < b) = true) :
    decide (a < floatInf) = true := by
  rw [decide_float_lt] at h ⊢
  have := unpacked_lt_left h
  show a.toModel.unpack.lt Float.Model.inf.unpack = true
  rw [inf_unpack]; exact unpacked_lt_inf this.1 this.2

theorem float_negInf_lt_of_lt {a b : Float} (h : decide (a < b) = true) :
    decide (floatNegInf < b) = true := by
  rw [decide_float_lt] at h ⊢
  have := unpacked_lt_right h
  show (-Float.Model.inf).unpack.lt b.toModel.unpack = true
  rw [negInf_unpack]; exact unpacked_negInf_lt this.1 this.2

theorem float_negInf_lt_of_zero_le {b : Float} (h : decide (floatZero ≤ b) = true) :
    decide (floatNegInf < b) = true := by
  rw [decide_float_le] at h
  rw [decide_float_lt]
  have := unpacked_le_right h (by rw [floatZero_unpack]; simp)
  show (-Float.Model.inf).unpack.lt b.toModel.unpack = true
  rw [negInf_unpack]; exact unpacked_negInf_lt this.1 this.2

end Order

/-! ## The shortened test chains -/

theorem uniform_checks {α : Type} (u : Float) (E r : Except Error α) :
    (if !decide (u < floatInf) then E
     else if !decide (floatNegInf < u) then E
     else if !decide (floatZero ≤ u) then E
     else if !decide (u < floatOne) then E
     else r) =
    (if !decide (floatZero ≤ u) then E
     else if !decide (u < floatOne) then E
     else r) := by
  by_cases h1 : decide (floatZero ≤ u) = true
  · by_cases h2 : decide (u < floatOne) = true
    · simp [float_lt_inf_of_lt h2, float_negInf_lt_of_zero_le h1, h1, h2]
    · simp only [Bool.not_eq_true] at h2
      simp [h1, h2]
  · simp only [Bool.not_eq_true] at h1
    simp [h1]

theorem exponential_checks {α : Type} (e : Float) (E r : Except Error α) :
    (if !decide (e < floatInf) then E
     else if !decide (floatNegInf < e) then E
     else if !decide (floatZero < e) then E
     else r) =
    (if !decide (e < floatInf) then E
     else if !decide (floatZero < e) then E
     else r) := by
  by_cases h1 : decide (floatZero < e) = true
  · simp [float_negInf_lt_of_lt h1, h1]
  · simp only [Bool.not_eq_true] at h1
    simp [h1]

theorem time_checks {α : Type} (now t : Float) (E r : Except Error α) :
    (if !decide (t < floatInf) then E
     else if !decide (floatNegInf < t) then E
     else if !decide (now < t) then E
     else if !decide (now ≤ t) then E
     else r) =
    (if !decide (t < floatInf) then E
     else if !decide (now < t) then E
     else r) := by
  by_cases h1 : decide (now < t) = true
  · simp [float_negInf_lt_of_lt h1, float_le_of_lt h1, h1]
  · simp only [Bool.not_eq_true] at h1
    simp [h1]

/-! ## Machine-word reads and the descent -/

theorem fget_eq (a : FloatArray) (i : USize) : Gen17.fget a i = a.get! i.toNat := by
  unfold Gen17.fget
  split
  · exact floatArray_uget_eq a i _
  · rfl

theorem aget_eq {α : Type} [Inhabited α] (a : Array α) (i : USize) :
    Gen17.aget a i = a[i.toNat]! := by
  unfold Gen17.aget
  split
  · rename_i h
    rw [getElem!_pos a i.toNat (Gen15.lt_size_of_lt_usize a i h)]; rfl
  · rfl

theorem changesAt_val (C : Gen6.Compiled) (n : Nat) (hval : Gen15.ValidChanges C n) (j : USize) :
    (Gen17.changesAt C n hval j).val = C.changes[j.toNat]! := by
  unfold Gen17.changesAt
  split
  · rename_i h
    show C.changes.uget j _ = _
    rw [getElem!_pos C.changes j.toNat (Gen15.lt_size_of_lt_usize C.changes j h)]; rfl
  · rfl

theorem usize_decide_lt (a b : USize) : decide (a < b) = decide (a.toNat < b.toNat) := by
  rfl

theorem descendW17_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (depth : Nat) (hPd : P.toNat = 2 ^ depth) :
    ∀ n i (k : USize) (hk0 : 0 < k.toNat) (x : Float), i + n = depth → 2 ^ i ≤ k.toNat →
      k.toNat < 2 ^ (i + 1) →
      (Gen17.descendW tree P hP hP2 k hk0 x).toNat = Gen1.descend tree n k.toNat x := by
  intro n
  induction n with
  | zero =>
    intro i k hk0 x hi hlo _
    obtain rfl : i = depth := by omega
    have hkP : ¬ k < P := by
      intro h
      have : k.toNat < P.toNat := h
      omega
    rw [Gen17.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
    rfl
  | succ n ih =>
    intro i k hk0 x hi hlo hhi
    have hpow : 2 ^ (i + 1) ≤ 2 ^ depth := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hkP' : k.toNat < P.toNat := by omega
    have hkP : k < P := hkP'
    have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
    have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
    have hs1 : 2 ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
    have hs0 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ]; omega
    rw [Gen17.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
    simp only [Gen1.descend, floatArray_uget_eq, h2]
    split
    · rw [← h2]
      exact ih (i + 1) (2 * k) _ x (by omega) (by rw [h2]; omega) (by rw [h2]; omega)
    · rw [show 2 * k.toNat + 1 = (2 * k + 1).toNat from h21.symm]
      exact ih (i + 1) (2 * k + 1) _ _ (by omega) (by rw [h21]; omega) (by rw [h21]; omega)

/-- The descent ends at a leaf: its node is at least `P`. -/
theorem descendW17_ge (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat = m →
      P.toNat ≤ (Gen17.descendW tree P hP hP2 k hk0 x).toNat := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro k hk0 x hm
    rw [Gen17.descendW]
    split
    · rename_i hk
      have hk' : k.toNat < P.toNat := hk
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      dsimp only
      split
      · exact ih (P.toNat - (2 * k).toNat) (by rw [h2]; omega) _ _ _ rfl
      · exact ih (P.toNat - (2 * k + 1).toNat) (by rw [h21]; omega) _ _ _ rfl
    · rename_i hk
      have : ¬ k.toNat < P.toNat := hk
      omega

/-! ## Firing in one loop -/

/-- No species is outside its bracket. -/
def NoStale (ms pop lo hi : Array Nat) (n : Nat) : Prop :=
  ∀ s < n, Gen9.staleI ms[s]! pop[s]! lo[s]! hi[s]! = false

theorem staleI_eq (ms n lo hi : Nat) :
    Gen9.staleI ms n lo hi = decide (n < lo ∨ hi < n ∨ (n < ms ∧ hi ≠ n)) := by
  unfold Gen9.staleI
  by_cases h1 : n < lo <;> by_cases h2 : hi < n <;> by_cases h3 : n < ms <;>
    by_cases h4 : hi = n <;> simp [h1, h2, h3, h4]

/-- After an addition only the upper end can be passed. -/
theorem staleI_up (ms old up lo hi : Nat) (h : Gen9.staleI ms old lo hi = false) :
    Gen9.staleI ms (old + up) lo hi = decide (hi < old + up) := by
  rw [staleI_eq] at h ⊢
  rw [decide_eq_false_iff_not] at h
  exact decide_eq_decide.mpr (by omega)

/-- After a removal only the lower end, or the maximal stoichiometry, can be passed. -/
theorem staleI_down (ms old down lo hi : Nat) (h : Gen9.staleI ms old lo hi = false) :
    Gen9.staleI ms (old - down) lo hi =
      (decide (old - down < lo) || (decide (old - down < ms) && hi != old - down)) := by
  rw [staleI_eq] at h ⊢
  rw [decide_eq_false_iff_not] at h
  have e : (decide (old - down < lo) || (decide (old - down < ms) && hi != old - down)) =
      decide (old - down < lo ∨ (old - down < ms ∧ hi ≠ old - down)) := by
    by_cases h1 : old - down < lo <;> by_cases h2 : old - down < ms <;>
      by_cases h3 : hi = old - down <;> simp [h1, h2, h3]
  rw [e]
  exact decide_eq_decide.mpr (by omega)

/-- Applying changes leaves the populations of other species alone. -/
theorem foldl_apply_get (L : List Gen6.Change) (pop : Array Nat) (s : Nat)
    (h : ∀ ch ∈ L, ch.species ≠ s) : (L.foldl Gen6.Change.apply pop)[s]! = pop[s]! := by
  induction L generalizing pop with
  | nil => rfl
  | cons ch L ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun ch' hch' => h ch' (List.mem_cons_of_mem _ hch'))]
    have hne := h ch (List.mem_cons_self ..)
    simp only [Gen6.Change.apply]
    exact Array.getElem!_set!_ne _ _ _ _ hne

theorem foldl_apply_size (L : List Gen6.Change) (pop : Array Nat) :
    (L.foldl Gen6.Change.apply pop).size = pop.size := by
  induction L generalizing pop with
  | nil => rfl
  | cons ch L ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [Gen6.Change.apply]

/-- `applyTest` from change `i` on applies the remaining changes and appends an entry exactly when
`stale` holds or some remaining changed species ends outside its bracket. -/
theorem applyTest_eq (chs : Array Gen6.Change) (n : Nat)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (ms lo hi : Array Nat) (hms : ms.size = n)
    (hlo : lo.size = n) (hhi : hi.size = n) (hsmall : chs.size < USize.size) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ (pop : Array Nat) (hp : pop.size = n) (stale : Bool),
      (∀ ch ∈ chs.toList.drop i.toNat, ch.up = 0 ∨ ch.down = 0) →
      ((chs.toList.drop i.toNat).map (·.species)).Nodup →
      (∀ ch ∈ chs.toList.drop i.toNat,
        Gen9.staleI ms[ch.species]! pop[ch.species]! lo[ch.species]! hi[ch.species]! = false) →
      Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale =
        if stale || (chs.toList.drop i.toNat).any (fun ch => Gen9.staleI ms[ch.species]!
            ((chs.toList.drop i.toNat).foldl Gen6.Change.apply pop)[ch.species]!
            lo[ch.species]! hi[ch.species]!)
        then ((chs.toList.drop i.toNat).foldl Gen6.Change.apply pop).push 0
        else (chs.toList.drop i.toNat).foldl Gen6.Change.apply pop := by
  intro m
  induction m with
  | zero =>
    intro i hm pop hp stale _ _ _
    have hi : chs.size ≤ i.toNat := by omega
    rw [Gen17.applyTest, dite_eq_right_iff.mpr (fun h => absurd (Gen15.lt_size_of_lt_usize chs i h)
      (by omega))]
    rw [List.drop_eq_nil_of_le (by simp; exact hi)]
    simp
  | succ m ih =>
    intro i hm pop hp stale hex hnd hst
    have hlt : i.toNat < chs.size := by omega
    have hiu : i < chs.usize := by
      show i.toNat < chs.usize.toNat
      rw [usize_toNat_eq chs hsmall]; exact hlt
    have h1 := Gen15.succ_toNat_of_lt_usize chs i hiu
    have hdrop : chs.toList.drop i.toNat = chs[i.toNat] :: chs.toList.drop (i + 1).toNat := by
      rw [h1, List.drop_eq_getElem_cons (by simp; exact hlt), Array.getElem_toList]
    rw [hdrop] at hex hnd hst ⊢
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot, hnd'⟩ := hnd
    have hne : ∀ ch' ∈ chs.toList.drop (i + 1).toNat, ch'.species ≠ chs[i.toNat].species := by
      intro ch' hch' he
      exact hnot (List.mem_map.mpr ⟨ch', hch', he⟩)
    have hs := hv _ hlt
    have hex0 := hex _ (List.mem_cons_self ..)
    have hst0 := hst _ (List.mem_cons_self ..)
    have hpop' : ∀ v (h : chs[i.toNat].species < pop.size),
        (pop.set chs[i.toNat].species v h) = pop.set! chs[i.toNat].species v := by
      intro v h
      simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, h, ↓reduceDIte]
    have hget : ∀ v, (List.foldl Gen6.Change.apply (pop.set! chs[i.toNat].species v)
        (chs.toList.drop (i + 1).toNat))[chs[i.toNat].species]! = v := by
      intro v
      rw [foldl_apply_get _ _ _ hne, Array.getElem!_set!_self _ _ _ (by rw [hp]; exact hs)]
    have hrest : ∀ v, ∀ ch ∈ chs.toList.drop (i + 1).toNat,
        Gen9.staleI ms[ch.species]! (pop.set! chs[i.toNat].species v)[ch.species]!
          lo[ch.species]! hi[ch.species]! = false := by
      intro v ch hch
      rw [Array.getElem!_set!_ne _ _ _ _ (hne ch hch).symm]
      exact hst ch (List.mem_cons_of_mem _ hch)
    have hps : chs[i.toNat].species < pop.size := by rw [hp]; exact hs
    rw [Gen17.applyTest, dite_eq_left_of_eq_true (eq_true hiu)]
    simp only [Array.uget, List.foldl_cons, List.any_cons]
    by_cases hd : chs[i.toNat].down = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
      rw [ih (i + 1) (by omega) _ _ _ (fun ch hch => hex ch (List.mem_cons_of_mem _ hch)) hnd'
        (by rw [hpop']; exact hrest _)]
      have happ : Gen6.Change.apply pop chs[i.toNat] =
          pop.set! chs[i.toNat].species (pop[chs[i.toNat].species] + chs[i.toNat].up) := by
        simp only [Gen6.Change.apply, hd, Nat.sub_zero, getElem!_pos pop chs[i.toNat].species hps]
      have := staleI_up ms[chs[i.toNat].species]! pop[chs[i.toNat].species]! chs[i.toNat].up
        lo[chs[i.toNat].species]! hi[chs[i.toNat].species]! hst0
      have hhs : chs[i.toNat].species < hi.size := by rw [hhi]; exact hs
      rw [getElem!_pos pop chs[i.toNat].species hps, getElem!_pos hi chs[i.toNat].species hhs] at this
      simp only [hpop', happ, hget, Bool.or_assoc,
        getElem!_pos hi chs[i.toNat].species hhs]
      rw [this]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
      have hu : chs[i.toNat].up = 0 := by
        rcases hex0 with h | h
        · exact h
        · exact absurd h hd
      rw [ih (i + 1) (by omega) _ _ _ (fun ch hch => hex ch (List.mem_cons_of_mem _ hch)) hnd'
        (by rw [hpop']; exact hrest _)]
      have happ : Gen6.Change.apply pop chs[i.toNat] =
          pop.set! chs[i.toNat].species (pop[chs[i.toNat].species] - chs[i.toNat].down) := by
        simp only [Gen6.Change.apply, hu, Nat.add_zero, getElem!_pos pop chs[i.toNat].species hps]
      have := staleI_down ms[chs[i.toNat].species]! pop[chs[i.toNat].species]! chs[i.toNat].down
        lo[chs[i.toNat].species]! hi[chs[i.toNat].species]! hst0
      have hhs : chs[i.toNat].species < hi.size := by rw [hhi]; exact hs
      have hls : chs[i.toNat].species < lo.size := by rw [hlo]; exact hs
      have hmss : chs[i.toNat].species < ms.size := by rw [hms]; exact hs
      rw [getElem!_pos pop chs[i.toNat].species hps] at this
      simp only [hpop', happ, hget, Bool.or_assoc, getElem!_pos hi chs[i.toNat].species hhs,
        getElem!_pos lo chs[i.toNat].species hls, getElem!_pos ms chs[i.toNat].species hmss]
      simp only [getElem!_pos hi chs[i.toNat].species hhs, getElem!_pos lo chs[i.toNat].species hls,
        getElem!_pos ms chs[i.toNat].species hmss] at this
      rw [this, Bool.or_assoc]

/-! ## No species leaves its bracket across an event -/

/-- A species is inside the bracket computed from its own count. -/
theorem staleI_bracket (ms x : Nat) :
    Gen9.staleI ms x (bracket ms x).1 (bracket ms x).2 = false := by
  rw [staleI_eq, decide_eq_false_iff_not]
  unfold bracket
  split
  · simp_all
  · split
    · simp only; omega
    · split
      · simp only; omega
      · simp only; omega

theorem rebracket13_lo (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (pop : Array Nat) (c : Cache) (s : Nat) :
    (Gen13.rebracket C codes P hP2 pop c s).lo = c.lo.set! s (bracket C.base.ms[s]! pop[s]!).1 ∧
      (Gen13.rebracket C codes P hP2 pop c s).hi = c.hi.set! s (bracket C.base.ms[s]! pop[s]!).2 :=
  ⟨rfl, rfl⟩

/-- A refresh changes only its own species' bracket. -/
theorem refresh13_other (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms pop : Array Nat) (c : Cache) (t s : Nat) (h : t ≠ s) :
    (Gen13.refresh C codes P hP2 ms pop c t).lo[s]! = c.lo[s]! ∧
      (Gen13.refresh C codes P hP2 ms pop c t).hi[s]! = c.hi[s]! := by
  unfold Gen13.refresh
  split
  · rw [(rebracket13_lo C codes P hP2 pop c t).1, (rebracket13_lo C codes P hP2 pop c t).2]
    exact ⟨Array.getElem!_set!_ne _ _ _ _ h, Array.getElem!_set!_ne _ _ _ _ h⟩
  · exact ⟨rfl, rfl⟩

/-- After its refresh a species is inside its bracket. -/
theorem refresh13_self (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (pop : Array Nat) (c : Cache) (t : Nat)
    (hlo : t < c.lo.size) (hhi : t < c.hi.size) :
    Gen9.staleI C.base.ms[t]! pop[t]! (Gen13.refresh C codes P hP2 C.base.ms pop c t).lo[t]!
      (Gen13.refresh C codes P hP2 C.base.ms pop c t).hi[t]! = false := by
  unfold Gen13.refresh
  split
  · rw [(rebracket13_lo C codes P hP2 pop c t).1, (rebracket13_lo C codes P hP2 pop c t).2,
      Array.getElem!_set!_self _ _ _ hlo, Array.getElem!_set!_self _ _ _ hhi]
    exact staleI_bracket _ _
  · rename_i h
    simpa using h

theorem refresh13_size (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms pop : Array Nat) (c : Cache) (t : Nat) :
    (Gen13.refresh C codes P hP2 ms pop c t).lo.size = c.lo.size ∧
      (Gen13.refresh C codes P hP2 ms pop c t).hi.size = c.hi.size := by
  unfold Gen13.refresh
  split
  · rw [(rebracket13_lo C codes P hP2 pop c t).1, (rebracket13_lo C codes P hP2 pop c t).2]
    exact ⟨Array.size_set! .., Array.size_set! ..⟩
  · exact ⟨rfl, rfl⟩

/-- Refreshing a list of distinct species: the others keep their brackets, the listed ones end
inside theirs. -/
theorem foldRefresh13_brackets (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (pop : Array Nat) (n : Nat) :
    ∀ (L : List Gen6.Change) (c : Cache), c.lo.size = n → c.hi.size = n →
      (∀ ch ∈ L, ch.species < n) → (L.map (·.species)).Nodup →
      let c' := L.foldl (fun c ch => Gen13.refresh C codes P hP2 C.base.ms pop c ch.species) c
      (∀ s, (∀ ch ∈ L, ch.species ≠ s) → c'.lo[s]! = c.lo[s]! ∧ c'.hi[s]! = c.hi[s]!) ∧
      (∀ ch ∈ L, Gen9.staleI C.base.ms[ch.species]! pop[ch.species]! c'.lo[ch.species]!
        c'.hi[ch.species]! = false) ∧ c'.lo.size = n ∧ c'.hi.size = n := by
  intro L
  induction L with
  | nil =>
    intro c hlo hhi _ _
    exact ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ h => absurd h List.not_mem_nil, hlo, hhi⟩
  | cons ch L ih =>
    intro c hlo hhi hv hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot, hnd'⟩ := hnd
    simp only [List.foldl_cons]
    have hsz := refresh13_size C codes P hP2 C.base.ms pop c ch.species
    obtain ⟨hother, hlisted, hlo', hhi'⟩ := ih (Gen13.refresh C codes P hP2 C.base.ms pop c ch.species)
      (by rw [hsz.1]; exact hlo) (by rw [hsz.2]; exact hhi)
      (fun ch' hch' => hv ch' (List.mem_cons_of_mem _ hch')) hnd'
    refine ⟨?_, ?_, hlo', hhi'⟩
    · intro s hs
      have h1 := hother s (fun ch' hch' => hs ch' (List.mem_cons_of_mem _ hch'))
      have h2 := refresh13_other C codes P hP2 C.base.ms pop c ch.species s (hs ch (List.mem_cons_self ..))
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
    · intro ch' hch'
      rcases List.mem_cons.mp hch' with rfl | hch'
      · have hnot' : ∀ ch'' ∈ L, ch''.species ≠ ch'.species := by
          intro ch'' hch'' he
          exact hnot (List.mem_map.mpr ⟨ch'', hch'', he⟩)
        have h1 := hother ch'.species hnot'
        rw [h1.1, h1.2]
        have hs := hv ch' (List.mem_cons_self ..)
        exact refresh13_self C codes P hP2 pop c ch'.species (by rw [hlo]; exact hs)
          (by rw [hhi]; exact hs)
      · exact hlisted ch' hch'

theorem changesOK_spec {C : Gen6.Compiled} (h : Gen17.changesOK C = true) (j : Nat) :
    (∀ ch ∈ (C.changes[j]!).toList, ch.up = 0 ∨ ch.down = 0) ∧
      ((C.changes[j]!).toList.map (·.species)).Nodup := by
  unfold Gen17.changesOK at h
  rw [Array.all_eq_true] at h
  by_cases hj : j < C.changes.size
  · have hj' := h j hj
    rw [Bool.and_eq_true, Array.all_eq_true] at hj'
    rw [getElem!_pos C.changes j hj]
    refine ⟨fun ch hch => ?_, by simpa using hj'.2⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hch
    have := hj'.1 k (by simpa using hk)
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    simpa using this
  · rw [getElem!_neg C.changes j hj]
    exact ⟨fun ch hch => absurd hch (by simp [show (default : Array Gen6.Change) = #[] from rfl]),
      by simp [show (default : Array Gen6.Change) = #[] from rfl]⟩

/-- Firing in one loop is generation 13's firing, and keeps every species inside its bracket. -/
theorem fire17 (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (n : Nat) (hms : C.gen5.base.ms.size = n) (j : Nat)
    (chs : Array Gen6.Change) (hchs : chs = C.changes[j]!)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (hsmall : chs.size < USize.size)
    (hex : ∀ ch ∈ chs.toList, ch.up = 0 ∨ ch.down = 0) (hnd : (chs.toList.map (·.species)).Nodup)
    (pop : Array Nat) (hpop : pop.size = n) (c : Cache) (hlo : c.lo.size = n)
    (hhi : c.hi.size = n) (hns : NoStale C.gen5.base.ms pop c.lo c.hi n) :
    let p := Gen17.applyTest chs n hv C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false
    let r := Gen13.fire C codes P hP2 C.gen5.base.ms pop c j
    (p.size = n → p = r.1 ∧ c = r.2) ∧
      (p.size ≠ n → p.pop = r.1 ∧
        chs.foldl (fun c ch => Gen16.refresh C.gen5 codes P hP2 C.gen5.base.ms p.pop c ch.species) c =
          r.2) ∧
      NoStale C.gen5.base.ms r.1 r.2.lo r.2.hi n := by
  intro p r
  have hvl : ∀ ch ∈ chs.toList, ch.species < n := by
    intro ch hch
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hch
    simp only [Array.getElem_toList]
    exact hv k (by simpa using hk)
  have hst : ∀ ch ∈ chs.toList,
      Gen9.staleI C.gen5.base.ms[ch.species]! pop[ch.species]! c.lo[ch.species]!
        c.hi[ch.species]! = false := fun ch hch => hns _ (hvl ch hch)
  have hp := applyTest_eq chs n hv C.gen5.base.ms c.lo c.hi hms hlo hhi hsmall _ 0 rfl pop hpop false
    (by simpa using hex) (by simpa using hnd) (by simpa using hst)
  simp only [USize.toNat_zero, List.drop_zero, Bool.false_or] at hp
  have hr1 : r.1 = chs.toList.foldl Gen6.Change.apply pop := by
    simp only [r, Gen13.fire, ← hchs, Array.foldl_toList]
  have hr2 : r.2 = chs.toList.foldl
      (fun c ch => Gen13.refresh C.gen5 codes P hP2 C.gen5.base.ms
        (chs.toList.foldl Gen6.Change.apply pop) c ch.species) c := by
    simp only [r, Gen13.fire, ← hchs, Array.foldl_toList]
  have hF : (chs.toList.foldl Gen6.Change.apply pop).size = n := by
    rw [foldl_apply_size]; exact hpop
  refine ⟨?_, ?_, ?_⟩
  · intro hps
    by_cases hS : (chs.toList.any fun ch => Gen9.staleI C.gen5.base.ms[ch.species]!
        (chs.toList.foldl Gen6.Change.apply pop)[ch.species]! c.lo[ch.species]!
        c.hi[ch.species]!) = true
    · exfalso
      have : p.size = n + 1 := by
        show (Gen17.applyTest chs n hv C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = _
        rw [hp, ite_eq_left_of_eq_true _ _ (eq_true hS), Array.size_push, hF]
      omega
    · have hp' : p = chs.toList.foldl Gen6.Change.apply pop := by
        show Gen17.applyTest chs n hv C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false = _
        rw [hp, ite_eq_right_of_eq_false _ _ (eq_false hS)]
      refine ⟨by rw [hp', hr1], ?_⟩
      rw [hr2]
      symm
      apply foldRefresh_id
      intro ch hch
      simp only [Bool.not_eq_true, List.any_eq_false] at hS
      simpa using hS ch hch
  · intro hps
    by_cases hS : (chs.toList.any fun ch => Gen9.staleI C.gen5.base.ms[ch.species]!
        (chs.toList.foldl Gen6.Change.apply pop)[ch.species]! c.lo[ch.species]!
        c.hi[ch.species]!) = true
    · have hp' : p = (chs.toList.foldl Gen6.Change.apply pop).push 0 := by
        show Gen17.applyTest chs n hv C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false = _
        rw [hp, ite_eq_left_of_eq_true _ _ (eq_true hS)]
      have hpp : p.pop = chs.toList.foldl Gen6.Change.apply pop := by rw [hp', Array.pop_push]
      refine ⟨by rw [hpp, hr1], ?_⟩
      rw [hr2, hpp, ← Array.foldl_toList]
      simp only [refresh16_eq]
    · exfalso
      apply hps
      show (Gen17.applyTest chs n hv C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = _
      rw [hp, ite_eq_right_of_eq_false _ _ (eq_false hS), hF]
  · intro s hs
    rw [hr1, hr2]
    obtain ⟨hother, hlisted, _, _⟩ := foldRefresh13_brackets C.gen5 codes P hP2
      (chs.toList.foldl Gen6.Change.apply pop) n chs.toList c hlo hhi hvl hnd
    by_cases hin : ∃ ch ∈ chs.toList, ch.species = s
    · obtain ⟨ch, hch, rfl⟩ := hin
      exact hlisted ch hch
    · have hne : ∀ ch ∈ chs.toList, ch.species ≠ s := fun ch hch he => hin ⟨ch, hch, he⟩
      obtain ⟨h1, h2⟩ := hother s hne
      rw [h1, h2, foldl_apply_get _ _ _ hne]
      exact hns s hs

/-! ## The driver -/

/-- What generation 17's driver keeps true between proposals: every species is inside its bracket,
and the total is the tree's root, finite and positive. -/
structure RunInv (ms : Array Nat) (n : Nat) (pop : Array Nat) (c : Cache) (total : Float) : Prop where
  noStale : NoStale ms pop c.lo c.hi n
  root : total = c.tree.get! 1
  ltInf : decide (total < floatInf) = true
  negInfLt : decide (floatNegInf < total) = true
  pos : decide (floatZero < total) = true

theorem of_not_not_true {b : Bool} (h : ¬ ((!b) = true)) : b = true := by
  cases b <;> simp_all

theorem usize_ne_zero_of_toNat {n : USize} {m : Nat} (h : n.toNat = m + 1) : n ≠ 0 := by
  intro h0; rw [h0] at h; simp at h

theorem usize_pred_toNat {n : USize} {m : Nat} (h : n.toNat = m + 1) : (n - 1).toNat = m := by
  rw [Gen16.pred_toNat n (usize_ne_zero_of_toNat h), h]; rfl

/-- Generation 17's driver from one proposal on is generation 16's, given the statement for the
next event. -/
theorem run17_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (n : Nat)
    (hms : C.gen5.base.ms.size = n) (hval : Gen15.ValidChanges C n)
    (hsmall : ∀ j : Nat, (C.changes[j]!).size < USize.size) (hok : Gen17.changesOK C = true)
    (P : USize) (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ C.gen5.base.depth)
    (hPl : P.toNat = C.gen5.base.leaves) (numRx : USize) (hnum : numRx.toNat = C.gen5.base.numRx)
    (horizon : Float) (save : Bool) (cap : USize) (fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ (evW prW : USize) pop hpop c hlo hhi now total elapsed s0 s1 s2
      s3 (count : USize) trace, evW.toNat = f → count.toNat + f < USize.size →
      RunInv C.gen5.base.ms n pop c total →
      Gen17.run C codes C.gen5.base.ms n hms hval numRx P hP2 C.gen5.base.rates
          C.gen5.base.factors horizon save cap evW prW pop hpop c hlo hhi now total elapsed s0 s1
          s2 s3 count trace =
        Gen16.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap.toNat f
          prW.toNat pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count.toNat trace) :
    ∀ prFuel (evW prW : USize) pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 (count : USize)
      trace, evW.toNat = fuel → prW.toNat = prFuel → count.toNat + fuel < USize.size →
      RunInv C.gen5.base.ms n pop c total →
      Gen17.run C codes C.gen5.base.ms n hms hval numRx P hP2 C.gen5.base.rates
          C.gen5.base.factors horizon save cap evW prW pop hpop c hlo hhi now total elapsed s0 s1
          s2 s3 count trace =
        Gen16.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap.toNat fuel
          prFuel pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count.toNat trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro evW prW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace hev hpr _ _
    have h0 : prW = 0 := USize.toNat_inj.mp (by rw [hpr]; rfl)
    rw [Gen17.run, dite_eq_left h0, Gen16.run.eq_1]
  | succ pf ih =>
    intro evW prW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace hev hpr hcount hinv
    rw [Gen17.run, dite_eq_right (usize_ne_zero_of_toNat hpr)]
    by_cases hT : 2 * P ≤ c.tree.usize
    · rw [dite_eq_left hT, Gen16.run.eq_2, dite_eq_left hT]
      simp only [uniform_checks, exponential_checks, time_checks]
      generalize hU : Xoshiro.uniform ⟨s0, s1, s2, s3⟩ = U
      obtain ⟨u, r1⟩ := U
      dsimp only
      have h1 : (1 : USize).toNat = 1 := by
        rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
      have hd17 := descendW17_eq c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2
        C.gen5.base.depth hPd C.gen5.base.depth 0 1 Gen11.usize_one_pos (u * total) (by omega)
        (by rw [h1]; simp) (by rw [h1]; simp)
      have hd16 := descendW16_eq c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2
        C.gen5.base.depth hPd C.gen5.base.depth 0 1 Gen11.usize_one_pos (u * total) (by omega)
        (by rw [h1]; simp) (by rw [h1]; simp)
      have hge := descendW17_ge c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 _ 1
        Gen11.usize_one_pos (u * total) rfl
      rw [h1] at hd17 hd16
      rw [hd16]
      have hPk : P ≤ Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
          Gen11.usize_one_pos (u * total) := hge
      have hkP : (Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
          Gen11.usize_one_pos (u * total) - P).toNat =
          Gen1.descend c.tree C.gen5.base.depth 1 (u * total) - C.gen5.base.leaves := by
        rw [USize.toNat_sub_of_le _ _ hPk, hd17, hPl]
      have hDl : C.gen5.base.leaves ≤ Gen1.descend c.tree C.gen5.base.depth 1 (u * total) := by
        rw [← hd17, ← hPl]; exact hge
      simp only [usize_decide_lt, fget_eq, aget_eq, hkP, hd17, hnum]
      rw [show C.gen5.base.leaves + (Gen1.descend c.tree C.gen5.base.depth 1 (u * total) -
        C.gen5.base.leaves) = Gen1.descend c.tree C.gen5.base.depth 1 (u * total) by omega]
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun hacc => ?_) (fun _ => ?_)
      · refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
        refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
        refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
        have hchs : (Gen17.changesAt C n hval (Gen17.descendW c.tree P
            (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).val =
            C.changes[Gen1.descend c.tree C.gen5.base.depth 1 (u * total) - C.gen5.base.leaves]! := by
          rw [changesAt_val, hkP]
        obtain ⟨hA, hB, hC⟩ := fire17 C codes P hP2 n hms
          (Gen1.descend c.tree C.gen5.base.depth 1 (u * total) - C.gen5.base.leaves) _ hchs
          (Gen17.changesAt C n hval (Gen17.descendW c.tree P
            (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).property
          (by rw [hchs]; exact hsmall _) (by rw [hchs]; exact (changesOK_spec hok _).1)
          (by rw [hchs]; exact (changesOK_spec hok _).2) pop hpop c hlo hhi hinv.noStale
        cases fuel with
        | zero =>
          have h0 : evW = 0 := USize.toNat_inj.mp (by rw [hev]; rfl)
          rw [dite_eq_left h0]
        | succ f =>
          rw [dite_eq_right (usize_ne_zero_of_toNat hev)]
          dsimp only
          rw [fire16_eq, fire15_mk C codes P hP2 _ n hms hval hsmall]
          dsimp only
          have hc1 : (count + 1).toNat = count.toNat + 1 := by
            have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
            rw [USize.toNat_add, h1]; exact Nat.mod_eq_of_lt (by omega)
          by_cases hps : (Gen17.applyTest (Gen17.changesAt C n hval (Gen17.descendW c.tree P
              (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).val
              n (Gen17.changesAt C n hval (Gen17.descendW c.tree P
              (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).property
              C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = n
          · rw [dite_eq_left hps]
            obtain ⟨hp1, hp2⟩ := hA hps
            have hC' := hC
            simp only [← hp1, ← hp2] at hC'
            simp only [← hp1, ← hp2, ← hinv.root, hinv.ltInf, hinv.negInfLt, hinv.pos, Bool.not_true,
              Bool.false_eq_true, ite_false]
            rw [← hc1]
            exact hnext f rfl (evW - 1) cap _ hps c hlo hhi _ total floatZero _ _ _ _ (count + 1) _
              (usize_pred_toNat hev) (by rw [hc1]; omega)
              ⟨hC', hinv.root, hinv.ltInf, hinv.negInfLt, hinv.pos⟩
          · rw [dite_eq_right hps]
            obtain ⟨hp1, hp2⟩ := hB hps
            simp only [h1, hp2]
            simp only [hp1]
            refine ite_congr rfl (fun _ => rfl) (fun hc1' => ?_)
            refine ite_congr rfl (fun _ => rfl) (fun hc2' => ?_)
            refine ite_congr rfl (fun _ => rfl) (fun hc3' => ?_)
            rw [← hc1]
            exact hnext f rfl (evW - 1) cap _ _ _ _ _ _ _ floatZero _ _ _ _ (count + 1) _
              (usize_pred_toNat hev) (by rw [hc1]; omega)
              ⟨hC, rfl, of_not_not_true hc1', of_not_not_true hc2', of_not_not_true hc3'⟩
      · exact ih evW (prW - 1) pop hpop c hlo hhi now total _ _ _ _ _ count trace hev
          (usize_pred_toNat hpr) hcount hinv
    · rw [dite_eq_right hT, hpr, hev, hPl, hnum]

theorem gen17_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (n : Nat)
    (hms : C.gen5.base.ms.size = n) (hval : Gen15.ValidChanges C n)
    (hsmall : ∀ j : Nat, (C.changes[j]!).size < USize.size) (hok : Gen17.changesOK C = true)
    (P : USize) (hP2 : 2 * P.toNat < USize.size) (hPd : P.toNat = 2 ^ C.gen5.base.depth)
    (hPl : P.toNat = C.gen5.base.leaves) (numRx : USize) (hnum : numRx.toNat = C.gen5.base.numRx)
    (horizon : Float) (save : Bool) (cap : USize) :
    ∀ fuel prFuel (evW prW : USize) pop hpop c hlo hhi now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = fuel → prW.toNat = prFuel →
      count.toNat + fuel < USize.size → RunInv C.gen5.base.ms n pop c total →
      Gen17.run C codes C.gen5.base.ms n hms hval numRx P hP2 C.gen5.base.rates
          C.gen5.base.factors horizon save cap evW prW pop hpop c hlo hhi now total elapsed s0 s1
          s2 s3 count trace =
        Gen16.run C codes C.gen5.base.ms n hms hval C.gen5.base.depth C.gen5.base.leaves
          C.gen5.base.numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon save cap.toNat fuel
          prFuel pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count.toNat trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run17_eq_of C codes n hms hval hsmall hok P hP2 hPd hPl numRx hnum horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    refine run17_eq_of C codes n hms hval hsmall hok P hP2 hPd hPl numRx hnum horizon save cap
      (f + 1) ?_
    intro f' hf' evW prW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace hev hcount hinv
    obtain rfl : f' = f := by omega
    exact ih prW.toNat evW prW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace hev rfl
      hcount hinv

theorem inBrackets_spec {ms pop lo hi : Array Nat} (h : Gen17.inBrackets ms pop lo hi = true) :
    NoStale ms pop lo hi ms.size := by
  intro s hs
  unfold Gen17.inBrackets at h
  rw [List.all_eq_true] at h
  have := h s (List.mem_range.mpr hs)
  simpa using this

theorem toUSize_toNat_of_lt {m : Nat} (h : m < USize.size) : m.toUSize.toNat = m := by
  rw [Nat.toUSize, USize.toNat_ofNat_of_lt' h]

theorem start17_eq (C : Gen6.Compiled) (codes : Array (Array Nat))
    (hC : C.gen5.base.leaves = 2 ^ C.gen5.base.depth) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) :
    Gen17.start C codes horizon save cap fuel pop c now rng count trace =
      Gen16.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen17.start
  by_cases hfin : Gen7.finite (c.tree.get! 1) = true
  · by_cases hpos : decide (floatZero < c.tree.get! 1) = true
    · by_cases h : 2 * C.gen5.base.leaves < USize.size
      · by_cases hs : pop.size = C.gen5.base.ms.size ∧ c.lo.size = C.gen5.base.ms.size ∧
            c.hi.size = C.gen5.base.ms.size ∧ Gen15.validChanges C C.gen5.base.ms.size = true ∧
            Gen17.changesOK C = true ∧ Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
            count + fuel < USize.size ∧ cap < USize.size ∧ C.gen5.base.numRx < USize.size
        · simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_left h,
            dite_eq_left hs]
          have hPl : C.gen5.base.leaves.toUSize.toNat = C.gen5.base.leaves :=
            toUSize_toNat_of_lt (by omega)
          have hPd : C.gen5.base.leaves.toUSize.toNat = 2 ^ C.gen5.base.depth := by rw [hPl, hC]
          have hfin' := hfin
          unfold Gen7.finite at hfin'
          rw [Bool.and_eq_true] at hfin'
          have hcnt : count < USize.size := by have := hs.2.2.2.2.2.2.1; omega
          have hfu : fuel < USize.size := by have := hs.2.2.2.2.2.2.1; omega
          have key := gen17_run_eq C codes C.gen5.base.ms.size rfl
            (Gen15.validChanges_spec hs.2.2.2.1) (validChanges_small hs.2.2.2.1) hs.2.2.2.2.1
            C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h) hPd hPl C.gen5.base.numRx.toUSize
            (toUSize_toNat_of_lt hs.2.2.2.2.2.2.2.2) horizon save cap.toUSize fuel cap fuel.toUSize
            cap.toUSize pop hs.1 c hs.2.1 hs.2.2.1 now (c.tree.get! 1) floatZero rng.s0 rng.s1 rng.s2
            rng.s3 count.toUSize trace (toUSize_toNat_of_lt hfu)
            (toUSize_toNat_of_lt hs.2.2.2.2.2.2.2.1)
            (by rw [toUSize_toNat_of_lt hcnt]; exact hs.2.2.2.2.2.2.1)
            ⟨inBrackets_spec hs.2.2.2.2.2.1, rfl, hfin'.1, hfin'.2, hpos⟩
          rw [key]
          unfold Gen16.start
          simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_left h,
            dite_eq_left (show pop.size = C.gen5.base.ms.size ∧ c.lo.size = C.gen5.base.ms.size ∧
              c.hi.size = C.gen5.base.ms.size ∧
              Gen15.validChanges C C.gen5.base.ms.size = true from
                ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩),
            toUSize_toNat_of_lt (show cap < USize.size from hs.2.2.2.2.2.2.2.1),
            toUSize_toNat_of_lt hcnt]
        · simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_left h,
            dite_eq_right hs]
      · simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_right h]
    · simp only [Bool.not_eq_true] at hpos
      unfold Gen16.start
      simp only [hfin, hpos, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
  · simp only [Bool.not_eq_true] at hfin
    unfold Gen16.start
    simp only [hfin, Bool.not_false, ite_true]

/-- Generation 17 returns what generation 16 returns, on every network and input. -/
theorem gen17_eq_gen16 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen17.simulate net initial start horizon rng maxEvents save cap =
      Gen16.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen17.simulate Gen16.simulate
  simp only [start17_eq _ _ (gen6_compile_leaves net)]

/-- **Generation 17 is the specification.** For every network whose reactant species are in
range and every input, generation 17 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen17_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen17.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen17_eq_gen16, gen16_simulate_eq net hwf]

end JumpProcessesLean.Proofs
