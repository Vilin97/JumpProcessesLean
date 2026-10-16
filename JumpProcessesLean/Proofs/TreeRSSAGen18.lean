import JumpProcessesLean.Proofs.TreeRSSAGen17
import JumpProcessesLean.Proofs.NativeCounts
import JumpProcessesLean.TreeRSSA.Gen18

/-!
# Generation 18 is generation 17, hence the specification

Generation 18 holds the populations and brackets as floats. Its arrays `pop`, `lo`, `hi` and the
maximal stoichiometries are related to generation 17's by `CountsOf`: entry `i` is `Float.ofNat` of
generation 17's entry. Every count stays below `2^26`, so by `Proofs/NativeCounts.lean` every sum,
positive difference, product and comparison generation 18 makes on them is the float of what
generation 17 computes on natural numbers.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)
open JumpProcessesLean.TreeRSSA.Gen7 (floatInf floatNegInf)
open JumpProcessesLean.Proofs.Counts

/-! ## Arrays of floats -/

theorem fa_size_set! (a : FloatArray) (i : Nat) (v : Float) : (a.set! i v).size = a.size := by
  cases a; simp [FloatArray.set!, FloatArray.size]

theorem fa_get!_set!_self (a : FloatArray) (i : Nat) (v : Float) (h : i < a.size) :
    (a.set! i v).get! i = v := by
  cases a with
  | mk d =>
    simp only [FloatArray.set!, FloatArray.get!]
    simp only [FloatArray.size] at h
    rw [Array.getElem!_set!_self]
    · exact h

theorem fa_get!_set!_ne (a : FloatArray) (i j : Nat) (v : Float) (h : i ≠ j) :
    (a.set! i v).get! j = a.get! j := by
  cases a with
  | mk d =>
    simp only [FloatArray.set!, FloatArray.get!]
    exact Array.getElem!_set!_ne _ _ _ _ h

theorem cget_eq (a : FloatArray) (i : USize) : Gen18.cget a i = a.get! i.toNat := fget_eq a i

theorem cset_eq (a : FloatArray) (i : USize) (v : Float) (h : i.toNat < a.size)
    (hs : a.size < USize.size) : Gen18.cset a i v = a.set! i.toNat v := by
  have hu : i < a.usize := by
    show i.toNat < a.usize.toNat
    simp only [FloatArray.usize, Nat.toUSize, USize.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by simpa [USize.size] using hs)]
    exact h
  unfold Gen18.cset
  rw [dite_eq_left hu]
  cases a with
  | mk d =>
    simp only [FloatArray.uset, FloatArray.set!, Array.uset]
    rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dite_eq_left (by simpa [FloatArray.size] using h)]

theorem fa_size_cset (a : FloatArray) (i : USize) (v : Float) : (Gen18.cset a i v).size = a.size := by
  unfold Gen18.cset
  split
  · cases a; simp only [FloatArray.uset, FloatArray.size, Array.uset]; exact Array.size_set ..
  · rfl

/-! ## Counts -/

/-- The first `n` entries of `a` are the floats of the natural numbers `xs`. -/
def CountsOf (a : FloatArray) (xs : Array Nat) (n : Nat) : Prop :=
  xs.size = n ∧ n ≤ a.size ∧ ∀ i < n, a.get! i = Float.ofNat xs[i]!

/-- All entries are below `2^26`. -/
def Small (xs : Array Nat) : Prop := ∀ i < xs.size, xs[i]! < 2 ^ 26

theorem ofCounts_eq {a : FloatArray} {xs : Array Nat} {n : Nat} (h : CountsOf a xs n)
    (hs : ∀ i < n, xs[i]! < 2 ^ 53) : Gen18.ofCounts a n = xs := by
  obtain ⟨hn, -, hv⟩ := h
  apply Array.ext
  · simp [Gen18.ofCounts, hn]
  · intro i h1 h2
    simp only [Gen18.ofCounts, Array.getElem_map, Array.getElem_range]
    rw [hv i (by simpa [Gen18.ofCounts] using h1), count_toUInt64 (hs i (by simpa [Gen18.ofCounts] using h1))]
    have := hs i (by simpa [Gen18.ofCounts] using h1)
    have h64 : xs[i]! < 18446744073709551616 := by omega
    rw [← getElem!_pos xs i h2]
    simp [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h64]

theorem toCounts_counts (xs : Array Nat) (hs : ∀ i < xs.size, xs[i]! < 2 ^ 64) :
    CountsOf (Gen18.toCounts xs) xs xs.size := by
  refine ⟨rfl, by simp [Gen18.toCounts, FloatArray.size], ?_⟩
  intro i hi
  simp only [Gen18.toCounts, FloatArray.get!]
  rw [getElem!_pos (xs.map natToFloat) i (by simpa using hi), Array.getElem_map,
    natToFloat_eq _ (by rw [← getElem!_pos xs i hi]; exact hs i hi), getElem!_pos xs i hi]

/-! ## Firing -/

theorem counts_set {a : FloatArray} {xs : Array Nat} {n : Nat} (h : CountsOf a xs n)
    (s : Nat) (hs : s < n) (v : Nat) :
    CountsOf (a.set! s (Float.ofNat v)) (xs.set! s v) n := by
  obtain ⟨hn, hle, hv⟩ := h
  refine ⟨by simp [hn], by rw [fa_size_set!]; exact hle, ?_⟩
  intro i hi
  by_cases his : i = s
  · subst his
    rw [fa_get!_set!_self _ _ _ (by omega), Array.getElem!_set!_self _ _ _ (by omega)]
  · rw [fa_get!_set!_ne _ _ _ _ (Ne.symm his), Array.getElem!_set!_ne _ _ _ _ (Ne.symm his), hv i hi]

theorem counts_get {a : FloatArray} {xs : Array Nat} {n : Nat} (h : CountsOf a xs n)
    {s : Nat} (hs : s < n) : a.get! s = Float.ofNat xs[s]! := h.2.2 s hs

theorem usize_toNat_toUSize {s n : Nat} (hs : s < n) (hn : n < USize.size) : s.toUSize.toNat = s :=
  toUSize_toNat_of_lt (by omega)

theorem map_uget {α β : Type} (a : Array α) (f : α → β) (i : USize) (h : i.toNat < (a.map f).size) :
    (a.map f).uget i h = f (a.uget i (by simpa using h)) := by
  simp [Array.uget]

theorem if_float_le (a b : Nat) (ha : a < 2 ^ 53) (hb : b < 2 ^ 53) {α : Type} (x y : α) :
    (if Float.ofNat a ≤ Float.ofNat b then x else y) = (if a ≤ b then x else y) := by
  have h := count_le ha hb
  by_cases hab : a ≤ b
  · have : Float.ofNat a ≤ Float.ofNat b := of_decide_eq_true (by rw [h]; simpa using hab)
    rw [ite_eq_left this, ite_eq_left hab]
  · have : ¬ Float.ofNat a ≤ Float.ofNat b := fun h' => by
      have := decide_eq_true h'; rw [h] at this; simp [hab] at this
    rw [ite_eq_right this, ite_eq_right hab]

/-- Firing on counts is generation 17's `applyTest`: the first `n` entries hold its populations,
and entry `n` flags whether it appended an entry. -/
theorem applyW_eq (chs : Array Gen6.Change) (n : Nat)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (ms lo hi : Array Nat) (hms : ms.size = n)
    (hlo : lo.size = n) (hhi : hi.size = n) (hcs : chs.size < USize.size)
    (msW loW hiW : FloatArray) (hmsW : CountsOf msW ms n) (hloW : CountsOf loW lo n)
    (hhiW : CountsOf hiW hi n) (hsm : ∀ s < n, ms[s]! < 2 ^ 26 ∧ lo[s]! < 2 ^ 26 ∧ hi[s]! < 2 ^ 26)
    (hamt : ∀ k (h : k < chs.size), chs[k].up < 2 ^ 26 ∧ chs[k].down < 2 ^ 26)
    (nW : USize) (hnW : nW.toNat = n) (hnU : n + 1 < USize.size) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ (pop : Array Nat) (hp : pop.size = n)
      (stale : Bool) (popW : FloatArray), CountsOf popW pop n → popW.size = n + 1 →
      ((chs.toList.drop i.toNat).map (·.species)).Nodup →
      (∀ ch ∈ chs.toList.drop i.toNat, pop[ch.species]! < 2 ^ 26) →
      CountsOf (Gen18.applyW (chs.map Gen18.ChangeW.ofChange) msW loW hiW nW i popW stale)
          (if (Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale).size = n then
            Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale
          else (Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale).pop) n ∧
        (Gen18.applyW (chs.map Gen18.ChangeW.ofChange) msW loW hiW nW i popW stale).size = n + 1 ∧
        (Gen18.applyW (chs.map Gen18.ChangeW.ofChange) msW loW hiW nW i popW stale).get! n =
          (if (Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale).size = n then floatZero
          else floatOne) := by
  intro m
  induction m with
  | zero =>
    intro i hm pop hp stale popW hc hsz _ _
    have hge : ¬ i < chs.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize chs i h; omega
    have hgeW : ¬ i < (chs.map Gen18.ChangeW.ofChange).usize := by simpa using hge
    rw [Gen17.applyTest, dite_eq_right hge, Gen18.applyW, dite_eq_right hgeW,
      cset_eq _ _ _ (by omega) (by omega), hnW]
    cases stale
    · simp only [Bool.false_eq_true, ite_false, hp, ite_true]
      refine ⟨⟨hp, by rw [fa_size_set!]; omega, fun i hi => ?_⟩, by rw [fa_size_set!, hsz], ?_⟩
      · rw [fa_get!_set!_ne _ _ _ _ (by omega), hc.2.2 i hi]
      · rw [fa_get!_set!_self _ _ _ (by omega)]
    · simp only [ite_true, Array.size_push, hp, Nat.succ_ne_self, ite_false, Array.pop_push]
      refine ⟨⟨hp, by rw [fa_size_set!]; omega, fun i hi => ?_⟩, by rw [fa_size_set!, hsz], ?_⟩
      · rw [fa_get!_set!_ne _ _ _ _ (by omega), hc.2.2 i hi]
      · rw [fa_get!_set!_self _ _ _ (by omega)]
  | succ m ih =>
    intro i hm pop hp stale popW hc hsz hnd hun
    have h : i < chs.usize := by
      show i.toNat < chs.usize.toNat
      simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by simpa [USize.size] using hcs)]
      omega
    have hW : i < (chs.map Gen18.ChangeW.ofChange).usize := by simpa using h
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    have h1 := Gen15.succ_toNat_of_lt_usize chs i h
    have hdrop : chs.toList.drop i.toNat = chs[i.toNat] :: chs.toList.drop (i + 1).toNat := by
      rw [h1, List.drop_eq_getElem_cons (by simpa using hi')]; simp
    rw [hdrop] at hnd hun
    have hnd' := (List.nodup_cons.mp (by simpa using hnd)).2
    have hns := (List.nodup_cons.mp (by simpa using hnd)).1
    have hs : chs[i.toNat].species < n := hv _ hi'
    have hold : pop[chs[i.toNat].species]! < 2 ^ 26 := hun _ (List.mem_cons_self ..)
    have hsmall := hsm _ hs
    have hamt' := hamt _ hi'
    have hsU : (chs[i.toNat].species).toUSize.toNat = chs[i.toNat].species :=
      usize_toNat_toUSize hs (by omega)
    have hps : chs[i.toNat].species < pop.size := by rw [hp]; exact hs
    have hns2 : chs[i.toNat].species ∉ List.map (fun x => x.species) (List.drop (i + 1).toNat chs.toList) :=
      (List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)).1
    have hun' : ∀ v, ∀ ch ∈ chs.toList.drop (i + 1).toNat,
        (pop.set! chs[i.toNat].species v)[ch.species]! < 2 ^ 26 := by
      intro v ch hch
      have hne : chs[i.toNat].species ≠ ch.species := by
        intro he; apply hns2; rw [List.mem_map]; exact ⟨ch, hch, he.symm⟩
      rw [Array.getElem!_set!_ne _ _ _ _ hne]
      exact hun ch (List.mem_cons_of_mem _ hch)
    rw [Gen17.applyTest, dite_eq_left_of_eq_true (eq_true h)]
    rw [Gen18.applyW, dite_eq_left hW]
    simp only [Array.uget, Array.getElem_map]
    by_cases hd : chs[i.toNat].down = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
      have hadd : (Gen18.ChangeW.ofChange chs[i.toNat]).add = true := by
        simp [Gen18.ChangeW.ofChange, hd]
      simp only [hadd, ite_true]
      have hhs : chs[i.toNat].species < hi.size := by rw [hhi]; exact hs
      have hpv : pop[chs[i.toNat].species] < 2 ^ 26 := by rw [← getElem!_pos pop _ hps]; exact hold
      have hhv : hi[chs[i.toNat].species] < 2 ^ 26 := by
        rw [← getElem!_pos hi _ hhs]; exact hsmall.2.2
      have hsp : (Gen18.ChangeW.ofChange chs[i.toNat]).species.toNat = chs[i.toNat].species := hsU
      have hamount : (Gen18.ChangeW.ofChange chs[i.toNat]).amount = Float.ofNat chs[i.toNat].up := by
        simp only [Gen18.ChangeW.ofChange, hd, beq_self_eq_true, ite_true]
        exact natToFloat_eq _ (by omega)
      have eA : Gen18.cget popW (Gen18.ChangeW.ofChange chs[i.toNat]).species +
          (Gen18.ChangeW.ofChange chs[i.toNat]).amount =
          Float.ofNat (pop[chs[i.toNat].species] + chs[i.toNat].up) := by
        rw [cget_eq, hsp, counts_get hc hs, hamount, getElem!_pos pop _ hps]
        exact count_add (by omega)
      have eB : decide (Gen18.cget hiW (Gen18.ChangeW.ofChange chs[i.toNat]).species <
          Float.ofNat (pop[chs[i.toNat].species] + chs[i.toNat].up)) =
          decide (hi[chs[i.toNat].species] < pop[chs[i.toNat].species] + chs[i.toNat].up) := by
        rw [cget_eq, hsp, counts_get hhiW hs, getElem!_pos hi _ hhs]
        exact count_lt (by omega) (by omega)
      rw [eA, eB, cset_eq _ _ _ (by rw [hsz, hsp]; omega) (by omega), hsp]
      have hset : pop.set chs[i.toNat].species (pop[chs[i.toNat].species] + chs[i.toNat].up) hps =
          pop.set! chs[i.toNat].species (pop[chs[i.toNat].species] + chs[i.toNat].up) := by
        simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, hps, ↓reduceDIte]
      have hc' : CountsOf (popW.set! chs[i.toNat].species
          (Float.ofNat (pop[chs[i.toNat].species] + chs[i.toNat].up)))
          (pop.set chs[i.toNat].species (pop[chs[i.toNat].species] + chs[i.toNat].up) hps) n := by
        rw [hset]; exact counts_set hc _ hs _
      have hnd2 : (List.map (fun x => x.species) (List.drop (i + 1).toNat chs.toList)).Nodup :=
        (List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)).2
      have hun2 : ∀ ch ∈ List.drop (i + 1).toNat chs.toList,
          (pop.set chs[i.toNat].species (pop[chs[i.toNat].species] + chs[i.toNat].up) hps)[ch.species]!
            < 2 ^ 26 := by
        rw [hset]; exact hun' _
      exact ih (i + 1) (by omega) _ (by simp [hp]) _ _ hc' (by rw [fa_size_set!, hsz]) hnd2 hun2
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
      have hadd : (Gen18.ChangeW.ofChange chs[i.toNat]).add = false := by
        simp [Gen18.ChangeW.ofChange, hd]
      simp only [hadd, Bool.false_eq_true, ite_false]
      have hhs : chs[i.toNat].species < hi.size := by rw [hhi]; exact hs
      have hls : chs[i.toNat].species < lo.size := by rw [hlo]; exact hs
      have hmss : chs[i.toNat].species < ms.size := by rw [hms]; exact hs
      have hpv : pop[chs[i.toNat].species] < 2 ^ 26 := by rw [← getElem!_pos pop _ hps]; exact hold
      have hhv : hi[chs[i.toNat].species] < 2 ^ 26 := by
        rw [← getElem!_pos hi _ hhs]; exact hsmall.2.2
      have hlv : lo[chs[i.toNat].species] < 2 ^ 26 := by
        rw [← getElem!_pos lo _ hls]; exact hsmall.2.1
      have hmv : ms[chs[i.toNat].species] < 2 ^ 26 := by
        rw [← getElem!_pos ms _ hmss]; exact hsmall.1
      have hsp : (Gen18.ChangeW.ofChange chs[i.toNat]).species.toNat = chs[i.toNat].species := hsU
      have hamount : (Gen18.ChangeW.ofChange chs[i.toNat]).amount = Float.ofNat chs[i.toNat].down := by
        simp only [Gen18.ChangeW.ofChange, hd, beq_iff_eq, ite_false]
        exact natToFloat_eq _ (by omega)
      have eA : (if Gen18.cget popW (Gen18.ChangeW.ofChange chs[i.toNat]).species ≤
            (Gen18.ChangeW.ofChange chs[i.toNat]).amount then floatZero
          else Gen18.cget popW (Gen18.ChangeW.ofChange chs[i.toNat]).species -
            (Gen18.ChangeW.ofChange chs[i.toNat]).amount) =
          Float.ofNat (pop[chs[i.toNat].species] - chs[i.toNat].down) := by
        rw [cget_eq, hsp, counts_get hc hs, hamount, getElem!_pos pop _ hps,
          if_float_le _ _ (by omega) (by omega)]
        split
        · rename_i hle; rw [Nat.sub_eq_zero_of_le hle]; rfl
        · rename_i hle; exact count_sub (by omega) (by omega)
      have eB : decide (Float.ofNat (pop[chs[i.toNat].species] - chs[i.toNat].down) <
          Gen18.cget loW (Gen18.ChangeW.ofChange chs[i.toNat]).species) =
          decide (pop[chs[i.toNat].species] - chs[i.toNat].down < lo[chs[i.toNat].species]) := by
        rw [cget_eq, hsp, counts_get hloW hs, getElem!_pos lo _ hls]
        exact count_lt (by omega) (by omega)
      have eC : decide (Float.ofNat (pop[chs[i.toNat].species] - chs[i.toNat].down) <
          Gen18.cget msW (Gen18.ChangeW.ofChange chs[i.toNat]).species) =
          decide (pop[chs[i.toNat].species] - chs[i.toNat].down < ms[chs[i.toNat].species]) := by
        rw [cget_eq, hsp, counts_get hmsW hs, getElem!_pos ms _ hmss]
        exact count_lt (by omega) (by omega)
      have eD : (Gen18.cget hiW (Gen18.ChangeW.ofChange chs[i.toNat]).species !=
          Float.ofNat (pop[chs[i.toNat].species] - chs[i.toNat].down)) =
          (hi[chs[i.toNat].species] != pop[chs[i.toNat].species] - chs[i.toNat].down) := by
        rw [cget_eq, hsp, counts_get hhiW hs, getElem!_pos hi _ hhs]
        simp only [bne, count_beq (by omega : hi[chs[i.toNat].species] < 2 ^ 53)
          (by omega : pop[chs[i.toNat].species] - chs[i.toNat].down < 2 ^ 53)]
      rw [eA, eB, eC, eD, cset_eq _ _ _ (by rw [hsz, hsp]; omega) (by omega), hsp]
      have hset : pop.set chs[i.toNat].species (pop[chs[i.toNat].species] - chs[i.toNat].down) hps =
          pop.set! chs[i.toNat].species (pop[chs[i.toNat].species] - chs[i.toNat].down) := by
        simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, hps, ↓reduceDIte]
      have hc' : CountsOf (popW.set! chs[i.toNat].species
          (Float.ofNat (pop[chs[i.toNat].species] - chs[i.toNat].down)))
          (pop.set chs[i.toNat].species (pop[chs[i.toNat].species] - chs[i.toNat].down) hps) n := by
        rw [hset]; exact counts_set hc _ hs _
      have hnd2 : (List.map (fun x => x.species) (List.drop (i + 1).toNat chs.toList)).Nodup :=
        (List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)).2
      have hun2 : ∀ ch ∈ List.drop (i + 1).toNat chs.toList,
          (pop.set chs[i.toNat].species (pop[chs[i.toNat].species] - chs[i.toNat].down) hps)[ch.species]!
            < 2 ^ 26 := by
        rw [hset]; exact hun' _
      exact ih (i + 1) (by omega) _ (by simp [hp]) _ _ hc' (by rw [fa_size_set!, hsz]) hnd2 hun2

/-! ## Refreshes -/

/-- The codes generation 18 accepts: `0`, `1`, or `4 (t + 1)` with `t < n`. -/
def CodeOK (n c : Nat) : Prop := c = 0 ∨ c = 1 ∨ (c % 4 = 0 ∧ 4 ≤ c ∧ c / 4 ≤ n)

/-- The record of a dependent with reaction `k`, code `c` and rate `r`. -/
def depOf (k c : Nat) (r : Float) : Gen18.DepW := ⟨k.toUSize, c == 1, (c / 4).toUSize, r⟩

theorem odd_iff {n c : Nat} (hc : CodeOK n c) : (c % 2 = 1) ↔ (c == 1) = true := by
  rcases hc with rfl | rfl | ⟨h4, h4', -⟩
  · simp
  · simp
  · have : c ≠ 1 := by omega
    simp [this]; omega

theorem partnerW_eq {n c k : Nat} {r : Float} (hc : CodeOK n c) (hn : n < USize.size)
    {arr : Array Nat} {arrW : FloatArray} (h : CountsOf arrW arr n) :
    Gen18.partnerW (depOf k c r) arrW = Float.ofNat (Gen13.partner c arr) := by
  unfold Gen18.partnerW depOf Gen13.partner
  rcases hc with rfl | rfl | ⟨h4, h4', hle⟩
  · simp; rfl
  · simp; rfl
  · have hU : (c / 4).toUSize.toNat = c / 4 := toUSize_toNat_of_lt (by omega)
    have hne : (c / 4).toUSize ≠ 0 := by
      intro h0; have := congrArg USize.toNat h0; rw [hU] at this; simp at this; omega
    rw [ite_eq_right hne, ite_eq_right (by omega), cget_eq]
    have h1 : ((c / 4).toUSize - 1).toNat = c / 4 - 1 := by
      rw [USize.toNat_sub_of_le _ _ (by
        show (1 : USize).toNat ≤ (c / 4).toUSize.toNat
        rw [hU]; rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h] <;> omega), hU]
      rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
    have hb : c / 2 % 2 = 0 := by omega
    rw [h1, counts_get h (by omega), hb]
    simp [Gen13.ffb]

theorem partner_lt {n c : Nat} (hc : CodeOK n c) {arr : Array Nat} (hs : ∀ t < n, arr[t]! < 2 ^ 26) :
    Gen13.partner c arr < 2 ^ 26 := by
  unfold Gen13.partner
  rcases hc with rfl | rfl | ⟨h4, h4', hle⟩
  · simp
  · simp
  · rw [ite_eq_right (by omega), show c / 2 % 2 = 0 by omega]
    simp only [Gen13.ffb, ite_true]
    exact hs _ (by omega)

/-- Generation 18's bound product is `natToFloat` of the integer product. -/
theorem bound_eq (a p : Nat) (ha : a < 2 ^ 52) (hp : p < 2 ^ 26) (hap : a * p < 2 ^ 52) (r : Float) :
    r * (Float.ofNat a * Float.ofNat p) = r * natToFloat (a * p) := by
  rw [count_mul (by omega) (by omega) (by omega), natToFloat_eq _ (by omega)]

theorem setBoundsW_eq (C : Gen3.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (hD : D.toNat = C.depth) (hPl : P.toNat = C.leaves) (n : Nat) (hn : n < USize.size)
    (lo hi : Array Nat) (loW hiW : FloatArray) (hloW : CountsOf loW lo n) (hhiW : CountsOf hiW hi n)
    (hlsm : ∀ t < n, lo[t]! < 2 ^ 26) (hhsm : ∀ t < n, hi[t]! < 2 ^ 26)
    (s loS hiS l0 m0 h0 g0 : Nat) (hl0 : l0 < 2 ^ 26) (hm0 : m0 < 2 ^ 26) (hh0 : h0 < 2 ^ 26)
    (hg0 : g0 < 2 ^ 26) (ks cs : Array Nat) (fs : Array Gen3.Factor) (rs : FloatArray)
    (hcs : cs.size = ks.size) (hrs : rs.size = ks.size) (hkU : ks.size < USize.size)
    (hcode : ∀ i < ks.size, CodeOK n cs[i]!) (hk : ∀ i < ks.size, ks[i]! < P.toNat) :
    ∀ m (i : USize), ks.size - i.toNat = m → ∀ (lower tree : FloatArray) (pW : USize) (pend : Nat),
      pW.toNat = pend →
      Gen18.setBoundsW P P hP2 D loW hiW (Float.ofNat l0) (Float.ofNat (l0 * (l0 - 1)))
          (Float.ofNat m0) (Float.ofNat (m0 * (m0 - 1))) (Float.ofNat h0)
          (Float.ofNat (h0 * (h0 - 1))) (Float.ofNat g0) (Float.ofNat (g0 * (g0 - 1)))
          ((Array.range ks.size).map fun i => depOf ks[i]! cs[i]! (rs.get! i)) i lower tree pW =
        Gen16.setBounds C P hP2 D lo hi s loS hiS l0 (l0 * (l0 - 1)) m0 (m0 * (m0 - 1)) h0
          (h0 * (h0 - 1)) g0 (g0 * (g0 - 1)) ks cs fs rs hcs hrs i lower tree pend := by
  intro m
  induction m with
  | zero =>
    intro i hm lower tree pW pend hp
    have hge : ¬ i < ks.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize ks i h; omega
    have hgeW : ¬ i < ((Array.range ks.size).map fun i => depOf ks[i]! cs[i]! (rs.get! i)).usize := by
      simpa using hge
    rw [Gen18.setBoundsW, dite_eq_right hgeW, Gen16.setBounds, dite_eq_right hge, hD, hp]
    congr 1
    by_cases h0 : pend = 0
    · have : pW = 0 := USize.toNat_inj.mp (by rw [hp, h0]; rfl)
      simp [this, h0]
    · have : pW ≠ 0 := fun h => h0 (by rw [← hp, h]; rfl)
      simp [this, h0]
  | succ m ih =>
    intro i hm lower tree pW pend hp
    have h : i < ks.usize := by
      show i.toNat < ks.usize.toNat
      simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by simpa [USize.size] using hkU)]
      omega
    have hW : i < ((Array.range ks.size).map fun i => depOf ks[i]! cs[i]! (rs.get! i)).usize := by
      simpa using h
    have hi' := Gen15.lt_size_of_lt_usize ks i h
    have hcs' : i.toNat < cs.size := by omega
    have hrs' : i.toNat < rs.size := by omega
    have hcok : CodeOK n cs[i.toNat] := by rw [← getElem!_pos cs i.toNat hcs']; exact hcode _ hi'
    have hkv : ks[i.toNat] < P.toNat := by rw [← getElem!_pos ks i.toNat hi']; exact hk _ hi'
    rw [Gen18.setBoundsW, dite_eq_left hW, Gen16.setBounds, dite_eq_left h]
    simp only [Array.uget, Array.getElem_map, Array.getElem_range, floatArray_uget_eq,
      getElem!_pos cs i.toNat hcs', getElem!_pos ks i.toNat hi']
    have hc2 : cs[i.toNat] ≠ 2 := by rcases hcok with h | h | h <;> omega
    simp only [hc2, ite_false]
    -- G18's record, factors and conditions in generation 16's terms
    have eTwo : ((depOf ks[i.toNat] cs[i.toNat] (rs.get! i.toNat)).two = true) =
        (cs[i.toNat] % 2 = 1) := propext (odd_iff hcok).symm
    have ePL := partnerW_eq (k := ks[i.toNat]) (r := rs.get! i.toNat) hcok hn hloW
    have ePH := partnerW_eq (k := ks[i.toNat]) (r := rs.get! i.toNat) hcok hn hhiW
    have hpL := partner_lt hcok hlsm
    have hpH := partner_lt hcok hhsm
    have hPU : P.toNat < USize.size :=
      lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by norm_num)) hP2
    have hk' : (depOf ks[i.toNat] cs[i.toNat] (rs.get! i.toNat)).k.toNat = ks[i.toNat] :=
      toUSize_toNat_of_lt (lt_trans hkv hPU)
    have hrate : (depOf ks[i.toNat] cs[i.toNat] (rs.get! i.toNat)).rate = rs.get! i.toNat := rfl
    have hleaf : (P + (depOf ks[i.toNat] cs[i.toNat] (rs.get! i.toNat)).k).toNat =
        C.leaves + ks[i.toNat] := by
      have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
      rw [USize.toNat_add, hk', hPl]; exact Nat.mod_eq_of_lt (by omega)
    simp only [eTwo, ePL, ePH, floatZero_eq, ← apply_ite Float.ofNat]
    have hsq : ∀ a : Nat, a < 2 ^ 26 → a * (a - 1) < 2 ^ 52 := by
      intro a ha
      calc a * (a - 1) ≤ a * a := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ < 2 ^ 26 * 2 ^ 26 := Nat.mul_lt_mul'' ha ha
        _ = 2 ^ 52 := by norm_num
    have hl1 := hsq l0 hl0
    have hm1 := hsq m0 hm0
    have hh1 := hsq h0 hh0
    have hg1 := hsq g0 hg0
    have hite : ∀ a : Nat, a < 2 ^ 26 →
        (if cs[i.toNat] % 2 = 1 then a * (a - 1) else a) < 2 ^ 52 := by
      intro a ha
      by_cases hc : cs[i.toNat] % 2 = 1
      · rw [ite_eq_left hc]; exact hsq a ha
      · rw [ite_eq_right hc]; omega
    have bAN := hite l0 hl0
    have bMM := hite m0 hm0
    have bBN := hite h0 hh0
    have bGG := hite g0 hg0
    -- the products are below 2^52: a squared own count has no partner
    have hprod : ∀ a : Nat, a < 2 ^ 26 → a * (a - 1) < 2 ^ 52 → ∀ x : Array Nat,
        Gen13.partner cs[i.toNat] x < 2 ^ 26 →
        (if cs[i.toNat] % 2 = 1 then a * (a - 1) else a) * Gen13.partner cs[i.toNat] x < 2 ^ 52 := by
      intro a ha ha1 x hp
      rcases hcok with h0c | h1c | ⟨h4, h4', hle⟩
      · rw [h0c]; simp [Gen13.partner]; omega
      · rw [h1c]; simp [Gen13.partner]; omega
      · rw [ite_eq_right (by omega)]
        calc a * Gen13.partner cs[i.toNat] x < 2 ^ 26 * 2 ^ 26 := Nat.mul_lt_mul_of_lt_of_lt ha hp
          _ = 2 ^ 52 := by norm_num
    have pLo := hprod l0 hl0 hl1 lo hpL
    have pHi := hprod h0 hh0 hh1 hi hpH
    have bAN' : (if cs[i.toNat] % 2 = 1 then l0 * (l0 - 1) else l0) < 2 ^ 53 := by omega
    have bMM' : (if cs[i.toNat] % 2 = 1 then m0 * (m0 - 1) else m0) < 2 ^ 53 := by omega
    have bBN' : (if cs[i.toNat] % 2 = 1 then h0 * (h0 - 1) else h0) < 2 ^ 53 := by omega
    have bGG' : (if cs[i.toNat] % 2 = 1 then g0 * (g0 - 1) else g0) < 2 ^ 53 := by omega
    rw [count_beq bAN' bMM', count_beq bBN' bGG', count_beq (by omega : Gen13.partner cs[i.toNat] lo < 2 ^ 53)
        (by norm_num : (0 : Nat) < 2 ^ 53),
      count_beq (by omega : Gen13.partner cs[i.toNat] hi < 2 ^ 53) (by norm_num : (0 : Nat) < 2 ^ 53),
      hrate, hk', hleaf, bound_eq _ _ (by omega) (by omega) pLo, bound_eq _ _ (by omega) (by omega) pHi]
    simp only [beq_iff_eq]
    rw [hD, hp]
    have hpz : (pW = 0) = (pend = 0) := propext ⟨fun h => by rw [← hp, h]; rfl,
      fun h => USize.toNat_inj.mp (by rw [hp, h]; rfl)⟩
    simp only [hpz]
    have hm' : ks.size - (i + 1).toNat = m := by rw [Gen15.succ_toNat_of_lt_usize ks i h]; omega
    split_ifs <;> first
      | exact ih (i + 1) hm' _ _ _ _ hp
      | exact ih (i + 1) hm' _ _ _ _ hleaf

theorem toUInt64_toNat_of_lt {a : Nat} (h : a < 2 ^ 64) : a.toUInt64.toNat = a := by
  have h' : a < 18446744073709551616 := by simpa using h
  simp [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h']

theorem bracketLo_eq (m x : Nat) (hm : m < 2 ^ 26) (hx : x < 2 ^ 26) :
    (Gen18.bracketLo m.toUInt64 x.toUInt64).toNat = (bracket m x).1 := by
  have hm' := toUInt64_toNat_of_lt (show m < 2 ^ 64 by omega)
  have hx' := toUInt64_toNat_of_lt (show x < 2 ^ 64 by omega)
  unfold Gen18.bracketLo bracket
  by_cases h0 : x = 0
  · subst h0; simp
  have h0' : x.toUInt64 ≠ 0 := fun h => h0 (by rw [← hx', h]; rfl)
  rw [ite_eq_right h0', ite_eq_right h0]
  by_cases h1 : x < m
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hx', hm']; exact h1), ite_eq_left h1, hx']
  rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hx', hm']; exact h1), ite_eq_right h1]
  by_cases h2 : x < 25
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hx']; simpa using h2), ite_eq_left h2]
    by_cases h3 : x < 4
    · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hx']; simpa using h3)]; simp; omega
    · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hx']; simpa using h3)]
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hx']; simp; omega), hx']
      simp
  · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hx']; simpa using h2), ite_eq_right h2]
    rw [UInt64.toNat_div, UInt64.toNat_mul, hx']
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (by omega)]

theorem bracketHi_eq (m x : Nat) (hm : m < 2 ^ 26) (hx : x < 2 ^ 26) :
    (Gen18.bracketHi m.toUInt64 x.toUInt64).toNat = (bracket m x).2 := by
  have hm' := toUInt64_toNat_of_lt (show m < 2 ^ 64 by omega)
  have hx' := toUInt64_toNat_of_lt (show x < 2 ^ 64 by omega)
  unfold Gen18.bracketHi bracket
  by_cases h0 : x = 0
  · subst h0; simp
  have h0' : x.toUInt64 ≠ 0 := fun h => h0 (by rw [← hx', h]; rfl)
  rw [ite_eq_right h0', ite_eq_right h0]
  by_cases h1 : x < m
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hx', hm']; exact h1), ite_eq_left h1, hx']
  rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hx', hm']; exact h1), ite_eq_right h1]
  by_cases h2 : x < 25
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hx']; simpa using h2), ite_eq_left h2]
    rw [UInt64.toNat_add, hx']
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hx']; simpa using h2), ite_eq_right h2]
    rw [UInt64.toNat_div, UInt64.toNat_mul, hx']
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (by omega)]

theorem bracket_lt (m x : Nat) (hx : x < 2 ^ 25) :
    (bracket m x).1 < 2 ^ 26 ∧ (bracket m x).2 < 2 ^ 26 := by
  unfold bracket
  split
  · simp
  · split
    · simp; omega
    · split
      · simp; omega
      · simp; omega

theorem ff2_eq (a : Nat) (ha : a < 2 ^ 26) : Gen18.ff2 (Float.ofNat a) = Float.ofNat (a * (a - 1)) := by
  unfold Gen18.ff2
  rw [floatOne_eq, if_float_le a 1 (by omega) (by omega)]
  by_cases h : a ≤ 1
  · rw [ite_eq_left h]
    have : a * (a - 1) = 0 := by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> rfl
    rw [this]; rfl
  · rw [ite_eq_right h, count_sub (by omega) (by omega)]
    exact count_mul (by omega) (by omega)
      (calc a * (a - 1) ≤ a * a := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ < 2 ^ 26 * 2 ^ 26 := Nat.mul_lt_mul'' ha ha
        _ < 2 ^ 53 := by norm_num)

/-! ## The compiled records -/

theorem compileW_ms (C : Gen6.Compiled) (codes : Array (Array Nat)) :
    (Gen18.compileW C codes).ms = Gen18.toCounts C.gen5.base.ms := rfl

theorem compileW_deps (C : Gen6.Compiled) (codes : Array (Array Nat)) (s : Nat)
    (hs : s < C.gen5.base.ms.size) :
    (Gen18.compileW C codes).deps[s]! =
      (Array.range (C.gen5.base.deps[s]!).size).map fun i =>
        depOf (C.gen5.base.deps[s]!)[i]! (codes[s]!)[i]! ((C.gen5.depRates[s]!).get! i) := by
  simp only [Gen18.compileW]
  rw [getElem!_pos _ s (by simpa using hs), Array.getElem_map, Array.getElem_range]
  rfl

theorem compileW_changes (C : Gen6.Compiled) (codes : Array (Array Nat)) (j : Nat)
    (hj : j < C.changes.size) :
    (Gen18.compileW C codes).changes[j]! = (C.changes[j]!).map Gen18.ChangeW.ofChange := by
  simp only [Gen18.compileW]
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos C.changes j hj]

theorem compileW_factors (C : Gen6.Compiled) (codes : Array (Array Nat)) (j : Nat)
    (hj : j < C.gen5.base.factors.size) :
    (Gen18.compileW C codes).factors[j]! = Gen18.FactorW.ofFactor C.gen5.base.factors[j]! := by
  simp only [Gen18.compileW]
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos _ j hj]

/-- Generation 18's rebracket of a species is generation 16's, on counts. -/
theorem rebracketW_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPl : P.toNat = C.gen5.base.leaves)
    (hdepth : C.gen5.base.depth < USize.size) (n : Nat) (hn : n + 1 < USize.size)
    (hms : C.gen5.base.ms.size = n) (hmsS : ∀ t < n, C.gen5.base.ms[t]! < 2 ^ 26)
    (pop : Array Nat) (popW : FloatArray) (hpop : CountsOf popW pop n)
    (c : Cache) (cW : Gen18.CacheW) (hlo : CountsOf cW.lo c.lo n) (hhi : CountsOf cW.hi c.hi n)
    (hlower : cW.lower = c.lower) (htree : cW.tree = c.tree)
    (hloS : ∀ t < n, c.lo[t]! < 2 ^ 26) (hhiS : ∀ t < n, c.hi[t]! < 2 ^ 26)
    (hlosz : cW.lo.size < USize.size) (hhisz : cW.hi.size < USize.size)
    (s : Nat) (hs : s < n) (hps : pop[s]! < 2 ^ 25)
    (hsz : (codes[s]!).size = (C.gen5.base.deps[s]!).size ∧
      (C.gen5.depRates[s]!).size = (C.gen5.base.deps[s]!).size ∧
      (C.gen5.base.deps[s]!).size < USize.size)
    (hcode : ∀ i < (C.gen5.base.deps[s]!).size, CodeOK n (codes[s]!)[i]!)
    (hk : ∀ i < (C.gen5.base.deps[s]!).size, (C.gen5.base.deps[s]!)[i]! < P.toNat) :
    CountsOf (Gen18.rebracketW (Gen18.compileW C codes) P P hP2 C.gen5.base.depth.toUSize popW cW
        s.toUSize).lo (Gen16.rebracket C.gen5 codes P hP2 pop c s).lo n ∧
      CountsOf (Gen18.rebracketW (Gen18.compileW C codes) P P hP2 C.gen5.base.depth.toUSize popW cW
        s.toUSize).hi (Gen16.rebracket C.gen5 codes P hP2 pop c s).hi n ∧
      (Gen18.rebracketW (Gen18.compileW C codes) P P hP2 C.gen5.base.depth.toUSize popW cW
        s.toUSize).lower = (Gen16.rebracket C.gen5 codes P hP2 pop c s).lower ∧
      (Gen18.rebracketW (Gen18.compileW C codes) P P hP2 C.gen5.base.depth.toUSize popW cW
        s.toUSize).tree = (Gen16.rebracket C.gen5 codes P hP2 pop c s).tree := by
  have hsU : s.toUSize.toNat = s := toUSize_toNat_of_lt (by omega)
  have hmsv := hmsS s hs
  have hb := bracket_lt C.gen5.base.ms[s]! pop[s]! hps
  -- the counts read by generation 18
  have ex : (Gen18.cget popW s.toUSize).toUInt64 = pop[s]!.toUInt64 := by
    rw [cget_eq, hsU, counts_get hpop hs, count_toUInt64 (by omega)]
  have em : (Gen18.cget (Gen18.compileW C codes).ms s.toUSize).toUInt64 =
      C.gen5.base.ms[s]!.toUInt64 := by
    have hc := toCounts_counts C.gen5.base.ms (fun t ht => by have := hmsS t (by omega); omega)
    rw [cget_eq, hsU, compileW_ms, counts_get hc (by omega), count_toUInt64 (by omega)]
  have eLoN : (Gen18.bracketLo (Gen18.cget (Gen18.compileW C codes).ms s.toUSize).toUInt64
      (Gen18.cget popW s.toUSize).toUInt64).toFloat = Float.ofNat (bracket C.gen5.base.ms[s]! pop[s]!).1 := by
    rw [ex, em, uint64_toFloat, bracketLo_eq _ _ hmsv (by omega)]
  have eHiN : (Gen18.bracketHi (Gen18.cget (Gen18.compileW C codes).ms s.toUSize).toUInt64
      (Gen18.cget popW s.toUSize).toUInt64).toFloat = Float.ofNat (bracket C.gen5.base.ms[s]! pop[s]!).2 := by
    rw [ex, em, uint64_toFloat, bracketHi_eq _ _ hmsv (by omega)]
  have eLoS : Gen18.cget cW.lo s.toUSize = Float.ofNat c.lo[s]! := by
    rw [cget_eq, hsU, counts_get hlo hs]
  have eHiS : Gen18.cget cW.hi s.toUSize = Float.ofNat c.hi[s]! := by
    rw [cget_eq, hsU, counts_get hhi hs]
  -- the new brackets
  have hlo' := counts_set hlo s hs (bracket C.gen5.base.ms[s]! pop[s]!).1
  have hhi' := counts_set hhi s hs (bracket C.gen5.base.ms[s]! pop[s]!).2
  have hloN : (c.lo.set! s (bracket C.gen5.base.ms[s]! pop[s]!).1)[s]! =
      (bracket C.gen5.base.ms[s]! pop[s]!).1 := Array.getElem!_set!_self _ _ _ (by rw [hlo.1]; exact hs)
  have hhiN : (c.hi.set! s (bracket C.gen5.base.ms[s]! pop[s]!).2)[s]! =
      (bracket C.gen5.base.ms[s]! pop[s]!).2 := Array.getElem!_set!_self _ _ _ (by rw [hhi.1]; exact hs)
  have hloSm : ∀ t < n, (c.lo.set! s (bracket C.gen5.base.ms[s]! pop[s]!).1)[t]! < 2 ^ 26 := by
    intro t ht
    by_cases hts : t = s
    · subst hts; rw [hloN]; exact hb.1
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hts)]; exact hloS t ht
  have hhiSm : ∀ t < n, (c.hi.set! s (bracket C.gen5.base.ms[s]! pop[s]!).2)[t]! < 2 ^ 26 := by
    intro t ht
    by_cases hts : t = s
    · subst hts; rw [hhiN]; exact hb.2
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hts)]; exact hhiS t ht
  have hD : (C.gen5.base.depth.toUSize).toNat = C.gen5.base.depth := toUSize_toNat_of_lt hdepth
  have key := setBoundsW_eq C.gen5.base P hP2 C.gen5.base.depth.toUSize hD hPl n (by omega)
    (c.lo.set! s (bracket C.gen5.base.ms[s]! pop[s]!).1) (c.hi.set! s (bracket C.gen5.base.ms[s]! pop[s]!).2)
    _ _ hlo' hhi' hloSm hhiSm s c.lo[s]! c.hi[s]! (bracket C.gen5.base.ms[s]! pop[s]!).1 c.lo[s]!
    (bracket C.gen5.base.ms[s]! pop[s]!).2 c.hi[s]! hb.1 (hloS s hs) hb.2 (hhiS s hs)
    (C.gen5.base.deps[s]!) (codes[s]!) (C.gen5.depFactors[s]!) (C.gen5.depRates[s]!) hsz.1 hsz.2.1 hsz.2.2
    hcode hk _ 0 rfl c.lower c.tree 0 0 rfl
  unfold Gen18.rebracketW Gen16.rebracket
  rw [dite_eq_left hsz]
  simp only []
  rw [eLoN, eHiN, eLoS, eHiS, ff2_eq _ hb.1, ff2_eq _ (hloS s hs), ff2_eq _ hb.2, ff2_eq _ (hhiS s hs),
    cset_eq _ _ _ (by rw [hsU]; have := hlo.2.1; omega) hlosz,
    cset_eq _ _ _ (by rw [hsU]; have := hhi.2.1; omega) hhisz, hsU, aget_eq, hsU,
    compileW_deps C codes s (by omega), hlower, htree, hloN, hhiN]
  refine ⟨hlo', hhi', ?_, ?_⟩
  · rw [key]
  · rw [key]

/-- Generation 18's cache holds generation 17's: the brackets as counts below `2^26`, the same
bounds and tree. -/
structure CacheRel (n : Nat) (cW : Gen18.CacheW) (c : Cache) : Prop where
  lo : CountsOf cW.lo c.lo n
  hi : CountsOf cW.hi c.hi n
  lower : cW.lower = c.lower
  tree : cW.tree = c.tree
  loSize : cW.lo.size = n
  hiSize : cW.hi.size = n
  loSmall : ∀ t < n, c.lo[t]! < 2 ^ 26
  hiSmall : ∀ t < n, c.hi[t]! < 2 ^ 26

theorem staleW_eq (m x l h : Nat) (hm : m < 2 ^ 53) (hx : x < 2 ^ 53) (hl : l < 2 ^ 53)
    (hh : h < 2 ^ 53) :
    Gen18.staleW (Float.ofNat m) (Float.ofNat x) (Float.ofNat l) (Float.ofNat h) =
      Gen9.staleI m x l h := by
  unfold Gen18.staleW Gen9.staleI
  rw [count_lt hx hl, count_lt hh hx, count_lt hx hm]
  simp only [bne, count_beq hh hx]

/-- The facts about species `s`'s dependents that generation 18's refresh needs. -/
def DepsOK (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize) (n s : Nat) : Prop :=
  ((codes[s]!).size = (C.gen5.base.deps[s]!).size ∧
    (C.gen5.depRates[s]!).size = (C.gen5.base.deps[s]!).size ∧
    (C.gen5.base.deps[s]!).size < USize.size) ∧
  (∀ i < (C.gen5.base.deps[s]!).size, CodeOK n (codes[s]!)[i]!) ∧
  (∀ i < (C.gen5.base.deps[s]!).size, (C.gen5.base.deps[s]!)[i]! < P.toNat)

theorem refreshFrom_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (hPl : P.toNat = C.gen5.base.leaves)
    (hdepth : C.gen5.base.depth < USize.size) (n : Nat) (hn : n + 1 < USize.size)
    (hms : C.gen5.base.ms.size = n) (hmsS : ∀ t < n, C.gen5.base.ms[t]! < 2 ^ 26)
    (hdeps : ∀ s < n, DepsOK C codes P n s)
    (chs : Array Gen6.Change) (hv : ∀ k (h : k < chs.size), chs[k].species < n)
    (hcs : chs.size < USize.size)
    (pop : Array Nat) (popW : FloatArray) (hpop : CountsOf popW pop n)
    (hpsm : ∀ ch ∈ chs.toList, pop[ch.species]! < 2 ^ 25) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ (c : Cache) (cW : Gen18.CacheW), CacheRel n cW c →
      CacheRel n (Gen18.refreshFrom (Gen18.compileW C codes) P P hP2 C.gen5.base.depth.toUSize
          (chs.map Gen18.ChangeW.ofChange) popW i cW)
        ((chs.toList.drop i.toNat).foldl
          (fun c ch => Gen16.refresh C.gen5 codes P hP2 C.gen5.base.ms pop c ch.species) c) := by
  intro m
  induction m with
  | zero =>
    intro i hm c cW hrel
    have hge : ¬ i < (chs.map Gen18.ChangeW.ofChange).usize := by
      intro h; have := Gen15.lt_size_of_lt_usize _ i h; simp at this; omega
    rw [Gen18.refreshFrom, dite_eq_right hge, List.drop_eq_nil_of_le (by simp; omega)]
    exact hrel
  | succ m ih =>
    intro i hm c cW hrel
    have h : i < chs.usize := by
      show i.toNat < chs.usize.toNat
      simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by simpa [USize.size] using hcs)]
      omega
    have hW : i < (chs.map Gen18.ChangeW.ofChange).usize := by simpa using h
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    have h1 := Gen15.succ_toNat_of_lt_usize chs i h
    have hdrop : chs.toList.drop i.toNat = chs[i.toNat] :: chs.toList.drop (i + 1).toNat := by
      rw [h1, List.drop_eq_getElem_cons (by simpa using hi')]; simp
    rw [Gen18.refreshFrom, dite_eq_left hW, hdrop, List.foldl_cons]
    simp only [Array.uget, Array.getElem_map, Gen18.ChangeW.ofChange]
    have hs := hv _ hi'
    have hsU : (chs[i.toNat].species).toUSize.toNat = chs[i.toNat].species :=
      toUSize_toNat_of_lt (by omega)
    have hps := hpsm chs[i.toNat] (Array.getElem_mem_toList hi')
    have hmsv := hmsS _ hs
    have hstale : Gen18.staleW (Gen18.cget (Gen18.compileW C codes).ms chs[i.toNat].species.toUSize)
        (Gen18.cget popW chs[i.toNat].species.toUSize) (Gen18.cget cW.lo chs[i.toNat].species.toUSize)
        (Gen18.cget cW.hi chs[i.toNat].species.toUSize) =
        Gen9.staleI C.gen5.base.ms[chs[i.toNat].species]! pop[chs[i.toNat].species]!
          c.lo[chs[i.toNat].species]! c.hi[chs[i.toNat].species]! := by
      have hc := toCounts_counts C.gen5.base.ms (fun t ht => by have := hmsS t (by omega); omega)
      rw [cget_eq, cget_eq, cget_eq, cget_eq, hsU, compileW_ms, counts_get hc (by omega),
        counts_get hpop hs, counts_get hrel.lo hs, counts_get hrel.hi hs]
      exact staleW_eq _ _ _ _ (by omega) (by omega) (by have := hrel.loSmall _ hs; omega)
        (by have := hrel.hiSmall _ hs; omega)
    rw [hstale]
    have hm' : chs.size - (i + 1).toNat = m := by omega
    unfold Gen16.refresh
    by_cases hst : Gen9.staleI C.gen5.base.ms[chs[i.toNat].species]! pop[chs[i.toNat].species]!
        c.lo[chs[i.toNat].species]! c.hi[chs[i.toNat].species]! = true
    · rw [ite_eq_left hst, ite_eq_left hst]
      apply ih (i + 1) hm'
      obtain ⟨hsz, hcode, hk⟩ := hdeps _ hs
      have hb := bracket_lt C.gen5.base.ms[chs[i.toNat].species]! pop[chs[i.toNat].species]! hps
      have key := rebracketW_eq C codes P hP2 hPl hdepth n hn hms hmsS pop popW hpop c cW hrel.lo
        hrel.hi hrel.lower hrel.tree hrel.loSmall hrel.hiSmall (by rw [hrel.loSize]; omega)
        (by rw [hrel.hiSize]; omega) _ hs hps hsz hcode hk
      rw [show chs[i.toNat].species.toUSize = (chs[i.toNat].species).toUSize from rfl] at key
      refine ⟨key.1, key.2.1, key.2.2.1, key.2.2.2, ?_, ?_, ?_, ?_⟩
      · unfold Gen18.rebracketW; simp only []
        rw [fa_size_cset, hrel.loSize]
      · unfold Gen18.rebracketW; simp only []
        rw [fa_size_cset, hrel.hiSize]
      · intro t ht
        unfold Gen16.rebracket; simp only []
        split <;> (by_cases hts : t = chs[i.toNat].species
                   · subst hts; rw [Array.getElem!_set!_self _ _ _ (by rw [hrel.lo.1]; exact ht)]; exact hb.1
                   · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hts)]; exact hrel.loSmall t ht)
      · intro t ht
        unfold Gen16.rebracket; simp only []
        split <;> (by_cases hts : t = chs[i.toNat].species
                   · subst hts; rw [Array.getElem!_set!_self _ _ _ (by rw [hrel.hi.1]; exact ht)]; exact hb.2
                   · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hts)]; exact hrel.hiSmall t ht)
    · simp only [Bool.not_eq_true] at hst
      rw [ite_eq_right (by simp [hst]), ite_eq_right (by simp [hst])]
      exact ih (i + 1) hm' c cW hrel

/-! ## The descent, the factors and the counts after firing -/

theorem descendW18_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      Gen18.descendW tree P hP hP2 k hk0 x = Gen17.descendW tree P hP hP2 k hk0 x := by
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [Gen18.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
      Gen17.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
  | succ m ih =>
    intro k hk0 x hm
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [Gen18.descendW, dite_eq_left_of_eq_true (eq_true hkP),
        Gen17.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega)
    · rw [Gen18.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
        Gen17.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]

theorem descendW18_eq' (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) :
    Gen18.descendW tree P hP hP2 k hk0 x = Gen17.descendW tree P hP hP2 k hk0 x :=
  descendW18_eq tree P hP hP2 _ k hk0 x le_rfl

theorem evalW_eq (f : Gen3.Factor) (n : Nat) (hok : Gen18.FactorW.ok n f = true)
    (hn : n < USize.size) (pop : Array Nat) (popW : FloatArray) (hpop : CountsOf popW pop n)
    (hsm : ∀ t < n, pop[t]! < 2 ^ 26) :
    Gen18.evalW (Gen18.FactorW.ofFactor f) popW = natToFloat (f.eval pop) := by
  have hcg : ∀ t < n, Gen18.cget popW t.toUSize = Float.ofNat pop[t]! := by
    intro t ht
    rw [cget_eq, toUSize_toNat_of_lt (by omega), counts_get hpop ht]
  cases f with
  | one t =>
    simp only [Gen18.FactorW.ok, decide_eq_true_eq] at hok
    simp only [Gen18.evalW, Gen18.FactorW.ofFactor, Gen3.Factor.eval, ite_true]
    rw [hcg t hok, natToFloat_eq _ (by have := hsm t hok; omega)]
  | two t =>
    simp only [Gen18.FactorW.ok, decide_eq_true_eq] at hok
    simp only [Gen18.evalW, Gen18.FactorW.ofFactor, Gen3.Factor.eval]
    have h0 : ¬ ((1 : UInt64) = 0) := by decide
    simp only [h0, ite_false, ite_true]
    rw [hcg t hok, ff2_eq _ (hsm t hok)]
    have := hsm t hok
    have hb : pop[t]! * (pop[t]! - 1) < 2 ^ 64 :=
      calc pop[t]! * (pop[t]! - 1) ≤ pop[t]! * pop[t]! := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ < 2 ^ 26 * 2 ^ 26 := Nat.mul_lt_mul'' this this
        _ < 2 ^ 64 := by norm_num
    rw [natToFloat_eq _ hb]
  | pair t ν u μ =>
    simp only [Gen18.FactorW.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨ht, hu⟩, rfl⟩, rfl⟩ := hok
    simp only [Gen18.evalW, Gen18.FactorW.ofFactor, Gen3.Factor.eval, Gen3.ff, ite_true]
    have h0 : ¬ ((2 : UInt64) = 0) := by decide
    have h1' : ¬ ((2 : UInt64) = 1) := by decide
    simp only [h0, h1', ite_false]
    rw [hcg t ht, hcg u hu]
    have h1 := hsm t ht
    have h2 := hsm u hu
    have hp : pop[t]! * pop[u]! < 2 ^ 52 :=
      calc pop[t]! * pop[u]! < 2 ^ 26 * 2 ^ 26 := Nat.mul_lt_mul'' h1 h2
        _ = 2 ^ 52 := by norm_num
    rw [count_mul (by omega) (by omega) (by omega), natToFloat_eq _ (by omega)]
  | general rs => simp [Gen18.FactorW.ok] at hok

theorem smallFrom_spec (chs : Array Gen6.Change) (n : Nat)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (hcs : chs.size < USize.size)
    (hn : n < USize.size) (pop : Array Nat) (popW : FloatArray) (hpop : CountsOf popW pop n)
    (h53 : ∀ t < n, pop[t]! < 2 ^ 53) :
    ∀ m (i : USize), chs.size - i.toNat = m →
      Gen18.smallFrom (chs.map Gen18.ChangeW.ofChange) popW i = true →
      ∀ ch ∈ chs.toList.drop i.toNat, pop[ch.species]! < 2 ^ 25 := by
  intro m
  induction m with
  | zero =>
    intro i hm _ ch hch
    rw [List.drop_eq_nil_of_le (by simp; omega)] at hch
    simp at hch
  | succ m ih =>
    intro i hm hsf ch hch
    have h : i < chs.usize := by
      show i.toNat < chs.usize.toNat
      simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by simpa [USize.size] using hcs)]
      omega
    have hW : i < (chs.map Gen18.ChangeW.ofChange).usize := by simpa using h
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    have h1 := Gen15.succ_toNat_of_lt_usize chs i h
    have hdrop : chs.toList.drop i.toNat = chs[i.toNat] :: chs.toList.drop (i + 1).toNat := by
      rw [h1, List.drop_eq_getElem_cons (by simpa using hi')]; simp
    rw [Gen18.smallFrom, dite_eq_left hW] at hsf
    simp only [Array.uget, Array.getElem_map, Gen18.ChangeW.ofChange] at hsf
    have hs := hv _ hi'
    rw [cget_eq, toUSize_toNat_of_lt (by omega), counts_get hpop hs] at hsf
    have hlt : decide (Float.ofNat pop[chs[i.toNat].species]! < Gen18.twoPow25) =
        decide (pop[chs[i.toNat].species]! < 33554432) :=
      count_lt (h53 _ hs) (by norm_num)
    by_cases h25 : pop[chs[i.toNat].species]! < 33554432
    · have : Float.ofNat pop[chs[i.toNat].species]! < Gen18.twoPow25 := by
        have := hlt; rw [decide_eq_true h25] at this; exact of_decide_eq_true this
      rw [ite_eq_left this] at hsf
      rw [hdrop] at hch
      rcases List.mem_cons.mp hch with rfl | hch'
      · simpa using h25
      · exact ih (i + 1) (by omega) hsf ch hch'
    · have : ¬ Float.ofNat pop[chs[i.toNat].species]! < Gen18.twoPow25 := by
        intro h'; have := decide_eq_true h'; rw [hlt] at this; simp at this; omega
      rw [ite_eq_right this] at hsf
      cases hsf

/-- After `applyTest` every count is below `2^27`; if it appended no entry, `stale` was false and
counts that were below `2^26` stay below `2^26`. -/
theorem applyTest_vals (chs : Array Gen6.Change) (n : Nat)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (ms lo hi : Array Nat) (hms : ms.size = n)
    (hlo : lo.size = n) (hhi : hi.size = n) (hcs : chs.size < USize.size)
    (hhiS : ∀ t < n, hi[t]! < 2 ^ 26)
    (hamt : ∀ k (h : k < chs.size), chs[k].up < 2 ^ 26 ∧ chs[k].down < 2 ^ 26) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ (pop : Array Nat) (hp : pop.size = n)
      (stale : Bool), ((chs.toList.drop i.toNat).map (·.species)).Nodup →
      (∀ ch ∈ chs.toList.drop i.toNat, pop[ch.species]! < 2 ^ 26) →
      (∀ t < n, pop[t]! < 2 ^ 27) →
      (∀ t < n, (if (Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale).size = n then
          Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale
        else (Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale).pop)[t]! < 2 ^ 27) ∧
      ((Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale).size = n →
        stale = false ∧ ((∀ t < n, pop[t]! < 2 ^ 26) →
          ∀ t < n, (Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale)[t]! < 2 ^ 26)) := by
  intro m
  induction m with
  | zero =>
    intro i hm pop hp stale _ _ h27
    have hge : ¬ i < chs.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize chs i h; omega
    rw [Gen17.applyTest, dite_eq_right hge]
    cases stale
    · simp only [Bool.false_eq_true, ite_false, hp, ite_true]
      exact ⟨h27, fun _ => ⟨trivial, fun h t ht => h t ht⟩⟩
    · simp only [ite_true, Array.size_push, hp, Nat.succ_ne_self, ite_false, Array.pop_push]
      refine ⟨h27, ?_⟩
      intro h0
      exfalso
      omega
  | succ m ih =>
    intro i hm pop hp stale hnd hun h27
    have h : i < chs.usize := by
      show i.toNat < chs.usize.toNat
      simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by simpa [USize.size] using hcs)]
      omega
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    have h1 := Gen15.succ_toNat_of_lt_usize chs i h
    have hdrop : chs.toList.drop i.toNat = chs[i.toNat] :: chs.toList.drop (i + 1).toNat := by
      rw [h1, List.drop_eq_getElem_cons (by simpa using hi')]; simp
    rw [hdrop] at hnd hun
    have hns2 : chs[i.toNat].species ∉ List.map (fun x => x.species) (List.drop (i + 1).toNat chs.toList) :=
      (List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)).1
    have hnd2 : (List.map (fun x => x.species) (List.drop (i + 1).toNat chs.toList)).Nodup :=
      (List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)).2
    have hs : chs[i.toNat].species < n := hv _ hi'
    have hps : chs[i.toNat].species < pop.size := by rw [hp]; exact hs
    have hold : pop[chs[i.toNat].species]! < 2 ^ 26 := hun _ (List.mem_cons_self ..)
    have hpv : pop[chs[i.toNat].species] < 2 ^ 26 := by rw [← getElem!_pos pop _ hps]; exact hold
    have hamt' := hamt _ hi'
    have hhs : chs[i.toNat].species < hi.size := by rw [hhi]; exact hs
    have hhv : hi[chs[i.toNat].species] < 2 ^ 26 := by rw [← getElem!_pos hi _ hhs]; exact hhiS _ hs
    have hrest : ∀ v, ∀ ch ∈ chs.toList.drop (i + 1).toNat,
        (pop.set chs[i.toNat].species v hps)[ch.species]! < 2 ^ 26 := by
      intro v ch hch
      have hne : chs[i.toNat].species ≠ ch.species := by
        intro he; apply hns2; rw [List.mem_map]; exact ⟨ch, hch, he.symm⟩
      have : (pop.set chs[i.toNat].species v hps) = pop.set! chs[i.toNat].species v := by
        simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, hps, ↓reduceDIte]
      rw [this, Array.getElem!_set!_ne _ _ _ _ hne]
      exact hun ch (List.mem_cons_of_mem _ hch)
    have hvals : ∀ v, v < 2 ^ 27 → ∀ t < n, (pop.set chs[i.toNat].species v hps)[t]! < 2 ^ 27 := by
      intro v hv t ht
      have : (pop.set chs[i.toNat].species v hps) = pop.set! chs[i.toNat].species v := by
        simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, hps, ↓reduceDIte]
      rw [this]
      by_cases hts : t = chs[i.toNat].species
      · subst hts; rw [Array.getElem!_set!_self _ _ _ hps]; exact hv
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hts)]; exact h27 t ht
    have hvals26 : ∀ v, v < 2 ^ 26 → (∀ t < n, pop[t]! < 2 ^ 26) →
        ∀ t < n, (pop.set chs[i.toNat].species v hps)[t]! < 2 ^ 26 := by
      intro v hv h26 t ht
      have : (pop.set chs[i.toNat].species v hps) = pop.set! chs[i.toNat].species v := by
        simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, hps, ↓reduceDIte]
      rw [this]
      by_cases hts : t = chs[i.toNat].species
      · subst hts; rw [Array.getElem!_set!_self _ _ _ hps]; exact hv
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hts)]; exact h26 t ht
    have hm' : chs.size - (i + 1).toNat = m := by omega
    rw [Gen17.applyTest, dite_eq_left_of_eq_true (eq_true h)]
    simp only [Array.uget]
    by_cases hd : chs[i.toNat].down = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
      have key := ih (i + 1) hm' (pop.set chs[i.toNat].species
        (pop[chs[i.toNat].species] + chs[i.toNat].up) hps) (by simp [hp])
        (stale || decide (hi[chs[i.toNat].species] < pop[chs[i.toNat].species] + chs[i.toNat].up))
        hnd2 (hrest _) (hvals _ (by omega))
      refine ⟨key.1, fun hsz => ?_⟩
      obtain ⟨hst, hb⟩ := key.2 hsz
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at hst
      exact ⟨hst.1, fun h26 => hb (hvals26 _ (by omega) h26)⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
      have hls : chs[i.toNat].species < lo.size := by rw [hlo]; exact hs
      have hmss : chs[i.toNat].species < ms.size := by rw [hms]; exact hs
      have key := ih (i + 1) hm' (pop.set chs[i.toNat].species
        (pop[chs[i.toNat].species] - chs[i.toNat].down) hps) (by simp [hp])
        (stale || decide (pop[chs[i.toNat].species] - chs[i.toNat].down < lo[chs[i.toNat].species]) ||
          (decide (pop[chs[i.toNat].species] - chs[i.toNat].down < ms[chs[i.toNat].species]) &&
            hi[chs[i.toNat].species] != pop[chs[i.toNat].species] - chs[i.toNat].down))
        hnd2 (hrest _) (hvals _ (by omega))
      refine ⟨key.1, fun hsz => ?_⟩
      obtain ⟨hst, hb⟩ := key.2 hsz
      simp only [Bool.or_eq_false_iff] at hst
      exact ⟨hst.1.1, fun h26 => hb (hvals26 _ (by omega) h26)⟩

/-- `applyTest` leaves the species it does not change alone. -/
theorem applyTest_other (chs : Array Gen6.Change) (n : Nat)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (ms lo hi : Array Nat) (hms : ms.size = n)
    (hlo : lo.size = n) (hhi : hi.size = n) (hcs : chs.size < USize.size) (t : Nat) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ (pop : Array Nat) (hp : pop.size = n)
      (stale : Bool), (∀ ch ∈ chs.toList.drop i.toNat, ch.species ≠ t) →
      (if (Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale).size = n then
          Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale
        else (Gen17.applyTest chs n hv ms lo hi hms hlo hhi i pop hp stale).pop)[t]! = pop[t]! := by
  intro m
  induction m with
  | zero =>
    intro i hm pop hp stale _
    have hge : ¬ i < chs.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize chs i h; omega
    rw [Gen17.applyTest, dite_eq_right hge]
    cases stale
    · simp [hp]
    · simp [hp]
  | succ m ih =>
    intro i hm pop hp stale hne
    have h : i < chs.usize := by
      show i.toNat < chs.usize.toNat
      simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by simpa [USize.size] using hcs)]
      omega
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    have h1 := Gen15.succ_toNat_of_lt_usize chs i h
    have hdrop : chs.toList.drop i.toNat = chs[i.toNat] :: chs.toList.drop (i + 1).toNat := by
      rw [h1, List.drop_eq_getElem_cons (by simpa using hi')]; simp
    rw [hdrop] at hne
    have hs : chs[i.toNat].species < n := hv _ hi'
    have hps : chs[i.toNat].species < pop.size := by rw [hp]; exact hs
    have hne0 : chs[i.toNat].species ≠ t := hne _ (List.mem_cons_self ..)
    have hne' : ∀ ch ∈ chs.toList.drop (i + 1).toNat, ch.species ≠ t :=
      fun ch hch => hne ch (List.mem_cons_of_mem _ hch)
    have hset : ∀ v, (pop.set chs[i.toNat].species v hps)[t]! = pop[t]! := by
      intro v
      have : (pop.set chs[i.toNat].species v hps) = pop.set! chs[i.toNat].species v := by
        simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, hps, ↓reduceDIte]
      rw [this, Array.getElem!_set!_ne _ _ _ _ hne0]
    have hm' : chs.size - (i + 1).toNat = m := by omega
    rw [Gen17.applyTest, dite_eq_left_of_eq_true (eq_true h)]
    simp only [Array.uget]
    by_cases hd : chs[i.toNat].down = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
      rw [ih (i + 1) hm' _ (by simp [hp]) _ hne', hset]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
      rw [ih (i + 1) hm' _ (by simp [hp]) _ hne', hset]

/-! ## The driver -/

/-- What generation 18's driver relies on, tested once by its start. -/
structure Static18 (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize) (n : Nat) : Prop where
  msSmall : ∀ t < n, C.gen5.base.ms[t]! < 2 ^ 26
  nU : n + 1 < USize.size
  depth : C.gen5.base.depth < USize.size
  leaves : P.toNat = C.gen5.base.leaves
  deps : ∀ s < n, DepsOK C codes P n s
  amounts : ∀ j : Nat, ∀ k (h : k < (C.changes[j]!).size),
    (C.changes[j]!)[k].up < 2 ^ 26 ∧ (C.changes[j]!)[k].down < 2 ^ 26
  changesSmall : ∀ j : Nat, (C.changes[j]!).size < USize.size
  nodup : ∀ j : Nat, ((C.changes[j]!).toList.map (·.species)).Nodup
  factors : ∀ j < C.gen5.base.factors.size, Gen18.FactorW.ok n C.gen5.base.factors[j]! = true
  numFactors : C.gen5.base.factors.size = C.gen5.base.numRx
  numChanges : C.gen5.base.numRx ≤ C.changes.size

/-- Generation 18's state holds generation 17's. -/
structure Rel18 (n : Nat) (popW : FloatArray) (cW : Gen18.CacheW) (pop : Array Nat) (c : Cache) :
    Prop where
  counts : CountsOf popW pop n
  size : popW.size = n + 1
  small : ∀ t < n, pop[t]! < 2 ^ 26
  cache : CacheRel n cW c

/-- Generation 18's firing of reaction `j` against generation 17's. -/
theorem fire18 (C : Gen6.Compiled) (codes : Array (Array Nat)) (n : Nat)
    (hms : C.gen5.base.ms.size = n) (hval : Gen15.ValidChanges C n) (P : USize)
    (hS : Static18 C codes P n) (popW : FloatArray) (loW hiW : FloatArray) (pop : Array Nat)
    (hpop : pop.size = n) (c : Cache) (hlo : c.lo.size = n) (hhi : c.hi.size = n)
    (hrel : Rel18 n popW ⟨loW, hiW, c.lower, c.tree⟩ pop c) (j : USize) :
    CountsOf (Gen18.applyW ((Gen17.changesAt C n hval j).1.map Gen18.ChangeW.ofChange)
        (Gen18.compileW C codes).ms loW hiW n.toUSize 0 popW false)
      (if (Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = n then
        Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false
      else (Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).pop) n ∧
    (Gen18.applyW ((Gen17.changesAt C n hval j).1.map Gen18.ChangeW.ofChange)
        (Gen18.compileW C codes).ms loW hiW n.toUSize 0 popW false).size = n + 1 ∧
    ((Gen18.cget (Gen18.applyW ((Gen17.changesAt C n hval j).1.map Gen18.ChangeW.ofChange)
        (Gen18.compileW C codes).ms loW hiW n.toUSize 0 popW false) n.toUSize == floatZero) =
      decide ((Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = n)) ∧
    (∀ t < n, (if (Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = n then
        Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false
      else (Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).pop)[t]! < 2 ^ 27) ∧
    ((Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = n →
      ∀ t < n, (Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false)[t]! < 2 ^ 26) ∧
    (∀ t < n, (∀ ch ∈ (Gen17.changesAt C n hval j).1.toList, ch.species ≠ t) →
      (if (Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = n then
        Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false
      else (Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
          C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).pop)[t]! = pop[t]!) := by
  have hval' := changesAt_val C n hval j
  have hcs : (Gen17.changesAt C n hval j).1.size < USize.size := by
    rw [hval']; exact hS.changesSmall _
  have hamt : ∀ k (h : k < (Gen17.changesAt C n hval j).1.size),
      (Gen17.changesAt C n hval j).1[k].up < 2 ^ 26 ∧ (Gen17.changesAt C n hval j).1[k].down < 2 ^ 26 := by
    intro k hk
    have := hS.amounts j.toNat k (by rw [← hval']; exact hk)
    simp only [hval'] at hk ⊢
    exact this
  have hnd : (((Gen17.changesAt C n hval j).1.toList.drop (0 : USize).toNat).map (·.species)).Nodup := by
    simp only [USize.toNat_zero, List.drop_zero, hval']; exact hS.nodup _
  have hun : ∀ ch ∈ (Gen17.changesAt C n hval j).1.toList.drop (0 : USize).toNat,
      pop[ch.species]! < 2 ^ 26 := by
    intro ch hch
    simp only [USize.toNat_zero, List.drop_zero] at hch
    have hk := List.mem_iff_getElem.mp hch
    obtain ⟨k, hk', rfl⟩ := hk
    exact hrel.small _ ((Gen17.changesAt C n hval j).2 k (by simpa using hk'))
  have hsm : ∀ s < n, C.gen5.base.ms[s]! < 2 ^ 26 ∧ c.lo[s]! < 2 ^ 26 ∧ c.hi[s]! < 2 ^ 26 :=
    fun s hs => ⟨hS.msSmall s hs, hrel.cache.loSmall s hs, hrel.cache.hiSmall s hs⟩
  have hmsW : CountsOf (Gen18.compileW C codes).ms C.gen5.base.ms n := by
    rw [compileW_ms, ← hms]
    exact toCounts_counts _ (fun t ht => by have := hS.msSmall t (by omega); omega)
  have hnW : n.toUSize.toNat = n := toUSize_toNat_of_lt (by have := hS.nU; omega)
  have hA := applyW_eq (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2 C.gen5.base.ms
    c.lo c.hi hms hlo hhi hcs _ loW hiW hmsW hrel.cache.lo hrel.cache.hi hsm hamt n.toUSize hnW hS.nU
    _ 0 rfl pop hpop false popW hrel.counts hrel.size hnd hun
  have hB := applyTest_vals (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
    C.gen5.base.ms c.lo c.hi hms hlo hhi hcs hrel.cache.hiSmall hamt _ 0 rfl pop hpop false hnd hun
    (fun t ht => by have := hrel.small t ht; omega)
  refine ⟨hA.1, hA.2.1, ?_, hB.1, fun h => (hB.2 h).2 hrel.small, ?_⟩
  · rw [cget_eq, hnW, hA.2.2]
    by_cases h : (Gen17.applyTest (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
        C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = n
    · simp only [h, ite_true, decide_true]; rfl
    · simp only [h, ite_false, decide_false]; rfl
  · intro t ht hne
    exact applyTest_other (Gen17.changesAt C n hval j).1 n (Gen17.changesAt C n hval j).2
      C.gen5.base.ms c.lo c.hi hms hlo hhi hcs t _ 0 rfl pop hpop false
      (by simpa using hne)

/-- The acceptance tests agree when the factors evaluate alike below `numRx`. -/
theorem acc18_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (numRx : USize) (popW : FloatArray)
    (pop : Array Nat) (hfg : ∀ j : USize, j < numRx →
      Gen18.evalW (Gen17.aget (Gen18.compileW C codes).factors j) popW =
        natToFloat ((Gen17.aget C.gen5.base.factors j).eval pop))
    (rates : FloatArray) (j : USize) (lower : FloatArray) (t : Float) :
    (if (!decide (j < numRx)) = true then false
     else if (decide (floatZero < Gen17.fget lower j) && decide (t ≤ Gen17.fget lower j)) = true then true
     else decide (floatZero < Gen17.fget rates j *
            Gen18.evalW (Gen17.aget (Gen18.compileW C codes).factors j) popW) &&
          decide (t ≤ Gen17.fget rates j *
            Gen18.evalW (Gen17.aget (Gen18.compileW C codes).factors j) popW)) =
    (if (!decide (j < numRx)) = true then false
     else if (decide (floatZero < Gen17.fget lower j) && decide (t ≤ Gen17.fget lower j)) = true then true
     else decide (floatZero < Gen17.fget rates j *
            natToFloat ((Gen17.aget C.gen5.base.factors j).eval pop)) &&
          decide (t ≤ Gen17.fget rates j *
            natToFloat ((Gen17.aget C.gen5.base.factors j).eval pop))) := by
  by_cases hj : j < numRx
  · rw [hfg j hj]
  · simp [hj]

theorem run18_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (n : Nat)
    (hms : C.gen5.base.ms.size = n) (hval : Gen15.ValidChanges C n)
    (P : USize) (hP2 : 2 * P.toNat < USize.size) (numRx : USize)
    (hnum : numRx.toNat = C.gen5.base.numRx) (hS : Static18 C codes P n)
    (horizon : Float) (save : Bool) (cap : USize) (fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ (evW prW : USize) popW cW pop hpop c hlo hhi now total elapsed s0 s1
      s2 s3 (count : USize) trace, evW.toNat = f → Rel18 n popW cW pop c →
      Gen18.run C codes (Gen18.compileW C codes) C.gen5.base.ms n hms hval n.toUSize numRx P hP2
          C.gen5.base.depth.toUSize C.gen5.base.rates horizon save cap evW prW popW cW now total elapsed
          s0 s1 s2 s3 count trace =
        Gen17.run C codes C.gen5.base.ms n hms hval numRx P hP2 C.gen5.base.rates C.gen5.base.factors
          horizon save cap evW prW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel (evW prW : USize) popW cW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = fuel → prW.toNat = prFuel → Rel18 n popW cW pop c →
      Gen18.run C codes (Gen18.compileW C codes) C.gen5.base.ms n hms hval n.toUSize numRx P hP2
          C.gen5.base.depth.toUSize C.gen5.base.rates horizon save cap evW prW popW cW now total elapsed
          s0 s1 s2 s3 count trace =
        Gen17.run C codes C.gen5.base.ms n hms hval numRx P hP2 C.gen5.base.rates C.gen5.base.factors
          horizon save cap evW prW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro evW prW popW cW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace hev hpr _
    have h0 : prW = 0 := USize.toNat_inj.mp (by rw [hpr]; rfl)
    rw [Gen18.run, dite_eq_left h0, Gen17.run, dite_eq_left h0]
  | succ pf ih =>
    intro evW prW popW cW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace hev hpr hrel
    have hnU := hS.nU
    have hnW : n.toUSize.toNat = n := toUSize_toNat_of_lt (by omega)
    have hcounts : Gen18.ofCounts popW n = pop :=
      ofCounts_eq hrel.counts (fun t ht => by have := hrel.small t ht; omega)
    have hclo : Gen18.ofCounts cW.lo n = c.lo :=
      ofCounts_eq hrel.cache.lo (fun t ht => by have := hrel.cache.loSmall t ht; omega)
    have hchi : Gen18.ofCounts cW.hi n = c.hi :=
      ofCounts_eq hrel.cache.hi (fun t ht => by have := hrel.cache.hiSmall t ht; omega)
    obtain ⟨loW, hiW, lowerW, treeW⟩ := cW
    have hlowerR : lowerW = c.lower := hrel.cache.lower
    have htreeR : treeW = c.tree := hrel.cache.tree
    subst hlowerR htreeR
    rw [Gen18.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen17.run,
      dite_eq_right (usize_ne_zero_of_toNat hpr)]
    by_cases hT : 2 * P ≤ c.tree.usize
    · rw [dite_eq_left hT, dite_eq_left hT]
      dsimp only
      generalize hU : Xoshiro.uniform ⟨s0, s1, s2, s3⟩ = U
      obtain ⟨u, r1⟩ := U
      dsimp only
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      generalize hE : r1.exponential = E
      obtain ⟨e, r2⟩ := E
      dsimp only
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      generalize hV : r2.uniform = V
      obtain ⟨v, r3⟩ := V
      dsimp only
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      simp only [descendW18_eq']
      have hevW : ∀ j : USize, j < numRx →
          Gen18.evalW (Gen17.aget (Gen18.compileW C codes).factors j) popW =
            natToFloat ((Gen17.aget C.gen5.base.factors j).eval pop) := by
        intro j hj
        have hjf : j.toNat < C.gen5.base.factors.size := by
          rw [hS.numFactors, ← hnum]; exact hj
        rw [aget_eq, aget_eq, compileW_factors C codes _ hjf]
        exact evalW_eq _ n (hS.factors _ hjf) (by omega) pop popW hrel.counts hrel.small
      rw [acc18_eq C codes numRx popW pop hevW]
      refine ite_congr rfl (fun hacc => ?_) (fun _ => ?_)
      · have hjn : Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
            Gen11.usize_one_pos (u * total) - P < numRx := by
          by_contra hj
          rw [ite_eq_left (by simp [hj])] at hacc
          cases hacc
        have hclo' : Gen18.ofCounts loW n = c.lo := hclo
        have hchi' : Gen18.ofCounts hiW n = c.hi := hchi
        refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
        refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
        refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
        refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
        · rw [hcounts, hclo', hchi']
        · refine dite_congr rfl (fun _ => rfl) (fun he => ?_)
          have hchW : ∀ j : USize, j < numRx → Gen17.aget (Gen18.compileW C codes).changes j =
              (Gen17.changesAt C n hval j).1.map Gen18.ChangeW.ofChange := by
            intro j hj
            have hjc : j.toNat < C.changes.size := by
              have := hS.numChanges; have : j.toNat < numRx.toNat := hj; omega
            rw [aget_eq, compileW_changes C codes _ hjc, changesAt_val]
          simp only [hchW _ hjn]
          obtain ⟨f1, f2, f3, f4, f5, f6⟩ := fire18 C codes n hms hval P hS popW loW hiW pop hpop c hlo hhi
            hrel (Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
              Gen11.usize_one_pos (u * total) - P)
          simp only [f3, decide_eq_true_eq]
          by_cases hps : (Gen17.applyTest (Gen17.changesAt C n hval (Gen17.descendW c.tree P
              (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1 n
              (Gen17.changesAt C n hval (Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT)
                hP2 1 Gen11.usize_one_pos (u * total) - P)).2
              C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).size = n
          · rw [ite_eq_left hps, dite_eq_left hps]
            have f1' := f1
            rw [ite_eq_left hps] at f1'
            rw [ofCounts_eq f1' (fun t ht => by have := f5 hps t ht; omega), hclo', hchi']
            have hev0 : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
            obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            exact hnext f hf (evW - 1) cap _ _ _ hps c hlo hhi _ total floatZero _ _ _ _ (count + 1) _
              (by rw [Gen16.pred_toNat evW he]; omega) ⟨f1', f2, f5 hps, hrel.cache⟩
          · rw [ite_eq_right hps, dite_eq_right hps]
            have f1' := f1
            rw [ite_eq_right hps] at f1'
            have hpp : Gen18.ofCounts (Gen18.applyW ((Gen17.changesAt C n hval (Gen17.descendW c.tree P
                (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1.map
                Gen18.ChangeW.ofChange) (Gen18.compileW C codes).ms loW hiW n.toUSize 0 popW false) n =
                (Gen17.applyTest (Gen17.changesAt C n hval (Gen17.descendW c.tree P
                  (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1 n
                  (Gen17.changesAt C n hval (Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT)
                    hP2 1 Gen11.usize_one_pos (u * total) - P)).2
                  C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).pop := by
              have h4 := f4
              simp only [ite_eq_right hps] at h4
              exact ofCounts_eq f1' (fun t ht => by have := h4 t ht; omega)
            have hcsz : (Gen17.changesAt C n hval (Gen17.descendW c.tree P
                (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1.size <
                USize.size := by rw [changesAt_val]; exact hS.changesSmall _
            by_cases hsf : Gen18.smallFrom ((Gen17.changesAt C n hval (Gen17.descendW c.tree P
                (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1.map
                Gen18.ChangeW.ofChange) (Gen18.applyW ((Gen17.changesAt C n hval (Gen17.descendW c.tree P
                (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1.map
                Gen18.ChangeW.ofChange) (Gen18.compileW C codes).ms loW hiW n.toUSize 0 popW false) 0 = true
            · rw [ite_eq_left hsf]
              have h4 := f4
              simp only [ite_eq_right hps] at h4
              have hsm25 := smallFrom_spec _ n (Gen17.changesAt C n hval _).2 hcsz (by omega) _ _ f1'
                (fun t ht => by have := h4 t ht; omega) _ 0 rfl hsf
              simp only [USize.toNat_zero, List.drop_zero] at hsm25
              have hR := refreshFrom_eq C codes P hP2 hS.leaves hS.depth n hS.nU hms hS.msSmall hS.deps
                _ (Gen17.changesAt C n hval _).2 hcsz _ _ f1' hsm25 _ 0 rfl c ⟨loW, hiW, c.lower, c.tree⟩
                hrel.cache
              simp only [USize.toNat_zero, List.drop_zero, Array.foldl_toList] at hR
              have e3 := ofCounts_eq hR.lo (fun t ht => by have := hR.loSmall t ht; omega)
              have e4 := ofCounts_eq hR.hi (fun t ht => by have := hR.hiSmall t ht; omega)
              rw [hpp, hR.tree, e3, e4]
              refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
              refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
              refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
              have hev0 : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
              obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
              refine hnext f hf (evW - 1) cap _ _ _ _ _ _ _ _ _ floatZero _ _ _ _ (count + 1) _
                (by rw [Gen16.pred_toNat evW he]; omega) ⟨f1', f2, ?_, hR⟩
              intro t ht
              by_cases hch : ∃ ch ∈ (Gen17.changesAt C n hval (Gen17.descendW c.tree P
                  (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1.toList,
                  ch.species = t
              · obtain ⟨ch, hch1, rfl⟩ := hch
                have := hsm25 ch hch1
                omega
              · push Not at hch
                have h6 := f6 t ht hch
                simp only [ite_eq_right hps] at h6
                rw [h6]; exact hrel.small t ht
            · rw [ite_eq_right hsf]
              have htc : Gen18.toCache n ⟨loW, hiW, c.lower, c.tree⟩ = c := by
                simp only [Gen18.toCache, hclo', hchi']
              have hsz := Gen16.foldRefresh_size C.gen5 codes P hP2 C.gen5.base.ms
                (Gen17.applyTest (Gen17.changesAt C n hval (Gen17.descendW c.tree P
                  (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1 n
                  (Gen17.changesAt C n hval (Gen17.descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT)
                    hP2 1 Gen11.usize_one_pos (u * total) - P)).2
                  C.gen5.base.ms c.lo c.hi hms hlo hhi 0 pop hpop false).pop
                (Gen17.changesAt C n hval (Gen17.descendW c.tree P
                  (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)).1 c
              simp only [hpp, htc, ← changesAt_val C n hval (Gen17.descendW c.tree P
                  (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos (u * total) - P)]
              rw [dite_eq_left f1'.1, dite_eq_left ⟨hsz.1.trans hlo, hsz.2.trans hhi⟩]
      · exact ih evW (prW - 1) popW ⟨loW, hiW, c.lower, c.tree⟩ pop hpop c hlo hhi now total _ _ _ _ _
          count trace hev (usize_pred_toNat hpr) hrel
    · rw [dite_eq_right hT, dite_eq_right hT]
      simp only [Gen18.toCache, hcounts, hclo, hchi]
      rw [dite_eq_left ⟨hpop, hlo, hhi⟩, Gen17.run]
      simp only [dite_eq_right hT, dite_eq_right (usize_ne_zero_of_toNat hpr)]

/-! ## The driver and the start -/

/-- Generation 18's driver returns what generation 17's returns. -/
theorem gen18_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (n : Nat)
    (hms : C.gen5.base.ms.size = n) (hval : Gen15.ValidChanges C n)
    (P : USize) (hP2 : 2 * P.toNat < USize.size) (numRx : USize)
    (hnum : numRx.toNat = C.gen5.base.numRx) (hS : Static18 C codes P n)
    (horizon : Float) (save : Bool) (cap : USize) :
    ∀ fuel prFuel (evW prW : USize) popW cW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = fuel → prW.toNat = prFuel → Rel18 n popW cW pop c →
      Gen18.run C codes (Gen18.compileW C codes) C.gen5.base.ms n hms hval n.toUSize numRx P hP2
          C.gen5.base.depth.toUSize C.gen5.base.rates horizon save cap evW prW popW cW now total
          elapsed s0 s1 s2 s3 count trace =
        Gen17.run C codes C.gen5.base.ms n hms hval numRx P hP2 C.gen5.base.rates
          C.gen5.base.factors horizon save cap evW prW pop hpop c hlo hhi now total elapsed s0 s1
          s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run18_eq_of C codes n hms hval P hP2 numRx hnum hS horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    refine run18_eq_of C codes n hms hval P hP2 numRx hnum hS horizon save cap (f + 1) ?_
    intro f' hf' evW prW popW cW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace hev
      hrel
    obtain rfl : f' = f := by omega
    exact ih prW.toNat evW prW popW cW pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace
      hev rfl hrel

theorem allSmall_spec {xs : Array Nat} (h : Gen18.allSmall xs = true) :
    ∀ t < xs.size, xs[t]! < 2 ^ 26 := by
  intro t ht
  unfold Gen18.allSmall at h
  rw [Array.all_eq_true] at h
  have := h t ht
  rw [getElem!_pos xs t ht]
  simpa using this

theorem fa_get!_push_lt (a : FloatArray) (v : Float) (i : Nat) (hi : i < a.size) :
    (a.push v).get! i = a.get! i := by
  cases a with
  | mk d =>
    simp only [FloatArray.push, FloatArray.get!]
    simp only [FloatArray.size] at hi
    rw [getElem!_pos (d.push v) i (by simp; omega), getElem!_pos d i hi, Array.getElem_push_lt]

theorem fa_size_push (a : FloatArray) (v : Float) : (a.push v).size = a.size + 1 := by
  cases a; simp [FloatArray.push, FloatArray.size]

theorem toCounts_size (xs : Array Nat) : (Gen18.toCounts xs).size = xs.size := by
  simp [Gen18.toCounts, FloatArray.size]

theorem counts_push {a : FloatArray} {xs : Array Nat} {n : Nat} (h : CountsOf a xs n)
    (v : Float) : CountsOf (a.push v) xs n := by
  obtain ⟨hn, hle, hv⟩ := h
  refine ⟨hn, by rw [fa_size_push]; omega, fun i hi => ?_⟩
  rw [fa_get!_push_lt a v i (by omega), hv i hi]

theorem depsOK_of_checks (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize) (n : Nat)
    (hP : P.toNat = C.gen5.base.leaves)
    (hcodes : codes.all (·.all fun c => c == 0 || c == 1 || (c % 4 == 0 && decide (4 ≤ c) &&
      decide (c / 4 ≤ n))) = true)
    (hcs : codes.size = n)
    (hd : (List.range n).all (fun s => (codes[s]!).size == (C.gen5.base.deps[s]!).size &&
      (C.gen5.depRates[s]!).size == (C.gen5.base.deps[s]!).size &&
      decide ((C.gen5.base.deps[s]!).size < USize.size) &&
      (C.gen5.base.deps[s]!).all (· < C.gen5.base.leaves)) = true) :
    ∀ s < n, DepsOK C codes P n s := by
  intro s hs
  rw [List.all_eq_true] at hd
  have h1 := hd s (List.mem_range.mpr hs)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at h1
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hdd⟩ := h1
  rw [Array.all_eq_true] at hcodes
  have hcs' : s < codes.size := by omega
  have h2 := hcodes s hcs'
  simp only [Array.all_eq_true] at h2
  refine ⟨⟨ha, hb, hc⟩, fun i hi => ?_, fun i hi => ?_⟩
  · rw [getElem!_pos codes s hcs'] at ha ⊢
    have hi' : i < codes[s].size := by omega
    have h3 := h2 i hi'
    rw [getElem!_pos codes[s] i hi']
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h3
    unfold CodeOK
    omega
  · rw [getElem!_pos _ i hi, hP]
    exact hdd i hi

theorem amounts_of_check {C : Gen6.Compiled}
    (h : C.changes.all (·.all fun ch => decide (ch.up < 67108864) && decide (ch.down < 67108864))
      = true) :
    ∀ j : Nat, ∀ k (hk : k < (C.changes[j]!).size),
      (C.changes[j]!)[k].up < 2 ^ 26 ∧ (C.changes[j]!)[k].down < 2 ^ 26 := by
  intro j k hk
  rw [Array.all_eq_true] at h
  by_cases hj : j < C.changes.size
  · have hjj := h j hj
    simp only [Array.all_eq_true] at hjj
    have hk' : k < (C.changes[j]).size := by rwa [getElem!_pos C.changes j hj] at hk
    have := hjj k hk'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [getElem!_pos C.changes j hj]
    exact ⟨by have := this.1; norm_num; omega, by have := this.2; norm_num; omega⟩
  · simp only [getElem!_neg C.changes j hj] at hk
    exact absurd hk (Nat.not_lt_zero k)

theorem factors_of_check {C : Gen6.Compiled} {n : Nat}
    (h : C.gen5.base.factors.all (Gen18.FactorW.ok n) = true) :
    ∀ j < C.gen5.base.factors.size, Gen18.FactorW.ok n C.gen5.base.factors[j]! = true := by
  intro j hj
  rw [Array.all_eq_true] at h
  rw [getElem!_pos C.gen5.base.factors j hj]
  exact h j hj

theorem gen6_compile_factors (net : Network Float) :
    (Gen6.compile net).gen5.base.factors.size = (Gen6.compile net).gen5.base.numRx := by
  simp [Gen6.compile, Gen5.compile, Gen3.compile]

theorem gen6_compile_changes (net : Network Float) :
    (Gen6.compile net).gen5.base.numRx ≤ (Gen6.compile net).changes.size := by
  simp [Gen6.compile, Gen5.compile, Gen3.compile]

theorem start18_eq (C : Gen6.Compiled) (codes : Array (Array Nat))
    (hC : C.gen5.base.leaves = 2 ^ C.gen5.base.depth)
    (hF : C.gen5.base.factors.size = C.gen5.base.numRx)
    (hCh : C.gen5.base.numRx ≤ C.changes.size) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) :
    Gen18.start C codes horizon save cap fuel pop c now rng count trace =
      Gen17.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen18.start
  by_cases hfin : Gen7.finite (c.tree.get! 1) = true
  · by_cases hpos : decide (floatZero < c.tree.get! 1) = true
    · by_cases h : 2 * C.gen5.base.leaves < USize.size
      · by_cases hs : pop.size = C.gen5.base.ms.size ∧ c.lo.size = C.gen5.base.ms.size ∧
            c.hi.size = C.gen5.base.ms.size ∧ Gen15.validChanges C C.gen5.base.ms.size = true ∧
            Gen17.changesOK C = true ∧ Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
            count + fuel < USize.size ∧ cap < USize.size ∧ C.gen5.base.numRx < USize.size ∧
            C.gen5.base.ms.size + 1 < USize.size ∧ Gen18.allSmall pop = true ∧
            Gen18.allSmall c.lo = true ∧ Gen18.allSmall c.hi = true ∧
            Gen18.allSmall C.gen5.base.ms = true ∧
            C.gen5.base.factors.all (Gen18.FactorW.ok C.gen5.base.ms.size) = true ∧
            codes.all (·.all fun c => c == 0 || c == 1 || (c % 4 == 0 && decide (4 ≤ c) &&
              decide (c / 4 ≤ C.gen5.base.ms.size))) = true ∧
            codes.size = C.gen5.base.ms.size ∧ C.gen5.depRates.size = C.gen5.base.ms.size ∧
            C.gen5.base.deps.size = C.gen5.base.ms.size ∧
            (List.range C.gen5.base.ms.size).all (fun s =>
              (codes[s]!).size == (C.gen5.base.deps[s]!).size &&
              (C.gen5.depRates[s]!).size == (C.gen5.base.deps[s]!).size &&
              decide ((C.gen5.base.deps[s]!).size < USize.size) &&
              (C.gen5.base.deps[s]!).all (· < C.gen5.base.leaves)) = true ∧
            C.changes.all (·.all fun ch => decide (ch.up < 67108864) &&
              decide (ch.down < 67108864)) = true
        · simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_left h,
            dite_eq_left hs]
          have hs' := hs
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
            h18, h19, h20, h21⟩ := hs'
          have hPl : C.gen5.base.leaves.toUSize.toNat = C.gen5.base.leaves :=
            toUSize_toNat_of_lt (by omega)
          have hS : Static18 C codes C.gen5.base.leaves.toUSize C.gen5.base.ms.size :=
            { msSmall := fun t ht => allSmall_spec h14 t ht
              nU := h10
              depth := by
                have := Nat.lt_two_pow_self (n := C.gen5.base.depth)
                omega
              leaves := hPl
              deps := depsOK_of_checks C codes _ _ hPl h16 h17 h20
              amounts := amounts_of_check h21
              changesSmall := validChanges_small h4
              nodup := fun j => (changesOK_spec h5 j).2
              factors := factors_of_check h15
              numFactors := hF
              numChanges := hCh }
          have hrel : Rel18 C.gen5.base.ms.size ((Gen18.toCounts pop).push 0)
              ⟨Gen18.toCounts c.lo, Gen18.toCounts c.hi, c.lower, c.tree⟩ pop c :=
            { counts := counts_push (h1 ▸ toCounts_counts pop (fun i hi => by
                have := allSmall_spec h11 i hi; omega)) 0
              size := by rw [fa_size_push, toCounts_size, h1]
              small := fun t ht => allSmall_spec h11 t (by omega)
              cache :=
                { lo := h2 ▸ toCounts_counts c.lo (fun i hi => by
                    have := allSmall_spec h12 i hi; omega)
                  hi := h3 ▸ toCounts_counts c.hi (fun i hi => by
                    have := allSmall_spec h13 i hi; omega)
                  lower := rfl
                  tree := rfl
                  loSize := by rw [toCounts_size, h2]
                  hiSize := by rw [toCounts_size, h3]
                  loSmall := fun t ht => allSmall_spec h12 t (by omega)
                  hiSmall := fun t ht => allSmall_spec h13 t (by omega) } }
          have hfu : fuel < USize.size := by omega
          rw [gen18_run_eq C codes C.gen5.base.ms.size rfl (Gen15.validChanges_spec h4) _
            (Gen11.leaves_toUSize h) C.gen5.base.numRx.toUSize (toUSize_toNat_of_lt h9) hS horizon
            save cap.toUSize fuel cap fuel.toUSize cap.toUSize _ _ pop h1 c h2 h3 now _ floatZero
            rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize trace (toUSize_toNat_of_lt hfu)
            (toUSize_toNat_of_lt h8) hrel]
          unfold Gen17.start
          simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_left h,
            dite_eq_left (show pop.size = C.gen5.base.ms.size ∧ c.lo.size = C.gen5.base.ms.size ∧
              c.hi.size = C.gen5.base.ms.size ∧
              Gen15.validChanges C C.gen5.base.ms.size = true ∧ Gen17.changesOK C = true ∧
              Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
              count + fuel < USize.size ∧ cap < USize.size ∧ C.gen5.base.numRx < USize.size from
                ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)]
        · simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_left h,
            dite_eq_right hs]
      · simp only [hfin, hpos, Bool.not_true, Bool.false_eq_true, ite_false, dite_eq_right h]
    · simp only [Bool.not_eq_true] at hpos
      unfold Gen17.start
      simp only [hfin, hpos, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false,
        ite_true]
  · simp only [Bool.not_eq_true] at hfin
    unfold Gen17.start
    simp only [hfin, Bool.not_false, ite_true]

/-- Generation 18 returns what generation 17 returns, on every network and input. -/
theorem gen18_eq_gen17 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen18.simulate net initial start horizon rng maxEvents save cap =
      Gen17.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen18.simulate Gen17.simulate
  simp only [start18_eq _ _ (gen6_compile_leaves net) (gen6_compile_factors net)
    (gen6_compile_changes net)]

/-- **Generation 18 is the specification.** For every network whose reactant species are in
range and every input, generation 18 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen18_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen18.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen18_eq_gen17, gen17_simulate_eq net hwf]

end JumpProcessesLean.Proofs
