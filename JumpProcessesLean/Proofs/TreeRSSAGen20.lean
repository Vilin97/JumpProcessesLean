import JumpProcessesLean.Proofs.TreeRSSAGen19
import JumpProcessesLean.TreeRSSA.Gen20

/-!
# Generation 20 is generation 19, hence the specification

Generation 20 computes what generation 19 computes, on the same state: each access with a proof
in bounds reads or writes what generation 19's tested access does, since the index is in range
(`fget_uget`, `cset_uset`), and each of its loops is generation 19's (`applyU_eq`, `smallU_eq`,
`setBoundsU_eq`, `refreshFromU_eq`). The driver's carried sizes make generation 19's tree size
test true, so the drivers agree (`gen20_run_eq`).
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)
open JumpProcessesLean.TreeRSSA.Gen7 (floatInf floatNegInf)

/-! ## Accesses -/

theorem fget_uget (a : FloatArray) (i : USize) (h : i.toNat < a.size) :
    Gen17.fget a i = a.uget i h := by
  rw [fget_eq, floatArray_uget_eq]

theorem cget_uget (a : FloatArray) (i : USize) (h : i.toNat < a.size) :
    Gen18.cget a i = a.uget i h := fget_uget a i h

theorem aget_uget {α : Type} [Inhabited α] (a : Array α) (i : USize) (h : i.toNat < a.size) :
    Gen17.aget a i = a.uget i h := by
  rw [aget_eq, getElem!_pos a i.toNat h]; rfl

theorem cset_uset (a : FloatArray) (i : USize) (v : Float) (h : i.toNat < a.size)
    (hs : a.size < USize.size) : Gen18.cset a i v = a.uset i v h := by
  rw [cset_eq a i v h hs, floatArray_uset_eq]

theorem descendW20_eq (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) :
    ∀ m (k : USize) (hk0 : 0 < k.toNat) (x : Float), P.toNat - k.toNat ≤ m →
      Gen20.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x := by
  intro m
  induction m with
  | zero =>
    intro k hk0 x hm
    have hkP : ¬ k < P := by intro h; have : k.toNat < P.toNat := h; omega
    rw [Gen20.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
      Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]
  | succ m ih =>
    intro k hk0 x hm
    by_cases hkP : k < P
    · have hk' : k.toNat < P.toNat := hkP
      have h2 : (2 * k).toNat = 2 * k.toNat := Gen11.usize_two_mul k (by omega)
      have h21 : (2 * k + 1).toNat = 2 * k.toNat + 1 := Gen11.usize_two_mul_add_one k (by omega)
      rw [Gen20.descendW, dite_eq_left_of_eq_true (eq_true hkP),
        Gen19.descendW, dite_eq_left_of_eq_true (eq_true hkP)]
      simp only []
      split
      · exact ih _ _ _ (by rw [h2]; omega)
      · exact ih _ _ _ (by rw [h21]; omega)
    · rw [Gen20.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP),
        Gen19.descendW, dite_eq_right_iff.mpr (fun h => absurd h hkP)]

/-! ## Firing -/

theorem applyU_eq (chs : Array Gen18.ChangeW) (nW : USize)
    (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat)
    (ms lo hi : FloatArray) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ (pop : FloatArray) (hpop : nW.toNat < pop.size)
      (_ : pop.size < USize.size) (stale : Bool),
      Gen20.applyU chs nW hchs ms lo hi hms hlo hhi i pop hpop stale =
        Gen18.applyW chs ms lo hi nW i pop stale := by
  intro m
  induction m with
  | zero =>
    intro i hm pop hpop hpopU stale
    have hge : ¬ i < chs.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize chs i h; omega
    rw [Gen20.applyU, dite_eq_right hge, Gen18.applyW, dite_eq_right hge, cset_uset _ _ _ hpop hpopU]
  | succ m ih =>
    intro i hm pop hpop hpopU stale
    by_cases h : i < chs.usize
    · have hs := Gen15.succ_toNat_of_lt_usize chs i h
      have hi' := Gen15.lt_size_of_lt_usize chs i h
      have hsp : (chs.uget i hi').species.toNat < nW.toNat := hchs i.toNat hi'
      rw [Gen20.applyU, dite_eq_left h, Gen18.applyW, dite_eq_left h]
      dsimp only
      rw [cget_uget pop _ (by omega)]
      split
      · rw [cset_uset _ _ _ (by omega) hpopU, cget_uget hi _ (by omega)]
        exact ih (i + 1) (by omega) _ _ (by rw [Gen20.size_uset]; exact hpopU) _
      · rw [cset_uset _ _ _ (by omega) hpopU, cget_uget lo _ (by omega), cget_uget ms _ (by omega),
          cget_uget hi _ (by omega)]
        exact ih (i + 1) (by omega) _ _ (by rw [Gen20.size_uset]; exact hpopU) _
    · rw [Gen20.applyU, dite_eq_right h, Gen18.applyW, dite_eq_right h, cset_uset _ _ _ hpop hpopU]

theorem smallU_eq (chs : Array Gen18.ChangeW) (nW : USize)
    (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) :
    ∀ m (i : USize), chs.size - i.toNat = m →
      Gen20.smallU chs nW hchs pop hpop i = Gen18.smallFrom chs pop i := by
  intro m
  induction m with
  | zero =>
    intro i hm
    have hge : ¬ i < chs.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize chs i h; omega
    rw [Gen20.smallU, dite_eq_right hge, Gen18.smallFrom, dite_eq_right hge]
  | succ m ih =>
    intro i hm
    by_cases h : i < chs.usize
    · have hs := Gen15.succ_toNat_of_lt_usize chs i h
      have hi' := Gen15.lt_size_of_lt_usize chs i h
      have hsp : (chs.uget i hi').species.toNat < nW.toNat := hchs i.toNat hi'
      rw [Gen20.smallU, dite_eq_left h, Gen18.smallFrom, dite_eq_left h]
      dsimp only
      rw [cget_uget pop _ (by omega), ih (i + 1) (by omega)]
    · rw [Gen20.smallU, dite_eq_right h, Gen18.smallFrom, dite_eq_right h]

theorem evalU_eq (f : Gen18.FactorW) (pop : FloatArray) (hs : f.s.toNat < pop.size)
    (ht : f.t.toNat < pop.size) : Gen20.evalU f pop hs ht = Gen18.evalW f pop := by
  simp only [Gen20.evalU, Gen18.evalW, cget_uget pop _ hs, cget_uget pop _ ht]

/-! ## Refreshes -/

theorem toUSize_toNat' (u : USize) : u.toNat.toUSize = u := by
  simp [Nat.toUSize]

theorem fixUntilAt_go (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray) (D : USize)
    (htree : 2 * P.toNat ≤ tree.size) (pending : USize) (hpn : pending.toNat < 2 * P.toNat)
    (other : USize) (hother : other.toNat < 2 * P.toNat) (hu : pending.toNat < tree.size) :
    Gen16.fixUntilAt P hP2 tree D.toNat D pending.toNat other.toNat =
      Gen16.fixUntilGo P D tree htree pending hpn other (tree.uget pending hu) := by
  unfold Gen16.fixUntilAt
  rw [dite_eq_left ⟨htree, hpn, hother, rfl⟩]
  simp only [toUSize_toNat']

theorem fixPathAt_go (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray) (D : USize)
    (htree : 2 * P.toNat ≤ tree.size) (pending : USize) (hpn : pending.toNat < 2 * P.toNat)
    (hu : pending.toNat < tree.size) :
    Gen16.fixPathAt P hP2 tree D.toNat D pending.toNat =
      Gen16.fixPathGo P D tree htree pending hpn (tree.uget pending hu) := by
  unfold Gen16.fixPathAt
  rw [dite_eq_left ⟨htree, hpn, rfl⟩]
  simp only [toUSize_toNat']

theorem setBoundsU_eq (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (nW : USize)
    (hi : FloatArray) (hhi : nW.toNat ≤ hi.size) (h0 h1 g0 g1 : Float) (ds : Array Gen18.DepW)
    (hds : ∀ k (h : k < ds.size),
      (ds[k]'h).k.toNat < P.toNat ∧ (ds[k]'h).partner.toNat ≤ nW.toNat) :
    ∀ m (i : USize), ds.size - i.toNat = m → ∀ (tree : FloatArray)
      (htree : 2 * P.toNat ≤ tree.size) (pending : USize) hpend,
      Gen20.setBoundsU P hP2 D nW hi hhi h0 h1 g0 g1 ds hds i tree htree pending hpend =
        Gen19.setBoundsV P P hP2 D hi h0 h1 g0 g1 ds i tree pending := by
  intro m
  induction m with
  | zero =>
    intro i hm tree htree pending hpend
    have hge : ¬ i < ds.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize ds i h; omega
    rw [Gen20.setBoundsU, dite_eq_right hge, Gen19.setBoundsV, dite_eq_right hge]
    by_cases hz : pending = 0
    · rw [dite_eq_left hz, ite_eq_left hz]
    · have hpn := hpend.resolve_left hz
      rw [dite_eq_right hz, ite_eq_right hz, fixPathAt_go P hP2 tree D htree pending hpn (by omega)]
  | succ m ih =>
    intro i hm tree htree pending hpend
    by_cases h : i < ds.usize
    · have hs := Gen15.succ_toNat_of_lt_usize ds i h
      have hi' := Gen15.lt_size_of_lt_usize ds i h
      have hd : (ds.uget i hi').k.toNat < P.toNat ∧ (ds.uget i hi').partner.toNat ≤ nW.toNat :=
        hds i.toNat hi'
      have hpH : (if hp : (ds.uget i hi').partner = 0 then floatOne
          else hi.uget ((ds.uget i hi').partner - 1) (by
            have : (ds.uget i hi').partner.toNat ≠ 0 :=
              fun h0 => hp (USize.toNat_inj.mp (by rw [h0]; rfl))
            rw [Gen20.usize_sub_one_toNat hp]; omega)) = Gen18.partnerW (ds.uget i hi') hi := by
        unfold Gen18.partnerW
        by_cases hp : (ds.uget i hi').partner = 0
        · rw [dite_eq_left hp, ite_eq_left hp]
        · have : (ds.uget i hi').partner.toNat ≠ 0 :=
            fun h0 => hp (USize.toNat_inj.mp (by rw [h0]; rfl))
          rw [dite_eq_right hp, ite_eq_right hp, cget_uget hi _ (by rw [Gen20.usize_sub_one_toNat hp]; omega)]
      rw [Gen20.setBoundsU, dite_eq_left h, Gen19.setBoundsV, dite_eq_left h]
      dsimp only
      simp only [hpH]
      by_cases c1 : ((if (ds.uget i hi').two = true then h1 else h0) ==
          (if (ds.uget i hi').two = true then g1 else g0)) = true
      · rw [ite_eq_left c1, ite_eq_left c1]
        exact ih (i + 1) (by omega) _ _ _ _
      · rw [ite_eq_right c1, ite_eq_right c1]
        by_cases c2 : (Gen18.partnerW (ds.uget i hi') hi == floatZero) = true
        · rw [ite_eq_left c2, ite_eq_left c2]
          exact ih (i + 1) (by omega) _ _ _ _
        · rw [ite_eq_right c2, ite_eq_right c2, ih (i + 1) (by omega)]
          have hleaf : (P + (ds.uget i hi').k).toNat = P.toNat + (ds.uget i hi').k.toNat := by
            have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
            rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
          congr 1
          by_cases hz : pending = 0
          · simp only [dite_eq_left hz, ite_eq_left hz]
            rw [floatArray_uset_eq]
          · have hpn := hpend.resolve_left hz
            simp only [dite_eq_right hz, ite_eq_right hz]
            rw [floatArray_uset_eq, fixUntilAt_go P hP2 tree D htree pending hpn _ (by omega)
              (by omega)]
    · rw [Gen20.setBoundsU, dite_eq_right h, Gen19.setBoundsV, dite_eq_right h]
      by_cases hz : pending = 0
      · rw [dite_eq_left hz, ite_eq_left hz]
      · have hpn := hpend.resolve_left hz
        rw [dite_eq_right hz, ite_eq_right hz, fixPathAt_go P hP2 tree D htree pending hpn (by omega)]

theorem rebracketU_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (c : Gen19.CacheV) (hc : Gen20.Sized nW P c)
    (s : USize) (hs : s.toNat < nW.toNat) :
    Gen20.rebracketU W P hP2 D nW numRx rates hB pop hpop c hc s hs =
      Gen19.rebracketV W P P hP2 D pop c s := by
  have hU := hB.nU
  have hms := hB.ms
  have hdeps := hB.deps
  have h1 := hc.1
  have h2 := hc.2.1
  simp only [Gen20.rebracketU, Gen19.rebracketV]
  rw [cget_uget pop s (by omega), cget_uget W.ms s (by omega), cget_uget c.hi s (by omega),
    cset_uset c.lo s _ (by omega) (by omega), cset_uset c.hi s _ (by omega) (by omega),
    aget_uget W.deps s (by omega)]
  congr 1
  exact setBoundsU_eq _ _ _ _ _ _ _ _ _ _ _ _ _ 0 rfl _ _ _ _

theorem refreshFromU_eq (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (chs : Array Gen18.ChangeW)
    (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) :
    ∀ m (i : USize), chs.size - i.toNat = m → ∀ (c : Gen19.CacheV) (hc : Gen20.Sized nW P c),
      Gen20.refreshFromU W P hP2 D nW numRx rates hB chs hchs pop hpop i c hc =
        Gen19.refreshFromV W P P hP2 D chs pop i c := by
  intro m
  induction m with
  | zero =>
    intro i hm c hc
    have hge : ¬ i < chs.usize := by
      intro h; have := Gen15.lt_size_of_lt_usize chs i h; omega
    rw [Gen20.refreshFromU, dite_eq_right hge, Gen19.refreshFromV, dite_eq_right hge]
  | succ m ih =>
    intro i hm c hc
    by_cases h : i < chs.usize
    · have hs := Gen15.succ_toNat_of_lt_usize chs i h
      have hi' := Gen15.lt_size_of_lt_usize chs i h
      have hsp : (chs.uget i hi').species.toNat < nW.toNat := hchs i.toNat hi'
      have hms := hB.ms
      have h1 := hc.1
      have h2 := hc.2.1
      rw [Gen20.refreshFromU, dite_eq_left h, Gen19.refreshFromV, dite_eq_left h]
      dsimp only
      rw [cget_uget W.ms _ (by omega), cget_uget pop _ (by omega), cget_uget c.lo _ (by omega),
        cget_uget c.hi _ (by omega)]
      split
      · rw [ih (i + 1) (by omega), rebracketU_eq]
      · exact ih (i + 1) (by omega) _ _
    · rw [Gen20.refreshFromU, dite_eq_right h, Gen19.refreshFromV, dite_eq_right h]

/-! ## The driver -/

theorem tree_usize (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray)
    (h : tree.size = 2 * P.toNat) : 2 * P ≤ tree.usize := by
  show (2 * P).toNat ≤ tree.usize.toNat
  rw [Gen11.usize_two_mul P hP2]
  simp only [FloatArray.usize, Nat.toUSize, USize.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by have hsz : USize.size = 2 ^ System.Platform.numBits := rfl; omega)]
  omega

theorem uget_fget (a : FloatArray) (i : USize) (h : i.toNat < a.size) :
    a.uget i h = Gen17.fget a i := (fget_uget a i h).symm

theorem auget_aget {α : Type} [Inhabited α] (a : Array α) (i : USize) (h : i.toNat < a.size) :
    a.uget i h = Gen17.aget a i := (aget_uget a i h).symm

theorem descendW20_eq' (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) :
    Gen20.descendW tree P hP hP2 k hk0 x = Gen19.descendW tree P hP hP2 k hk0 x :=
  descendW20_eq tree P hP hP2 _ k hk0 x le_rfl

theorem applyU_eq' (chs : Array Gen18.ChangeW) (nW : USize)
    (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat)
    (ms lo hi : FloatArray) (hms : nW.toNat ≤ ms.size) (hlo : nW.toNat ≤ lo.size)
    (hhi : nW.toNat ≤ hi.size) (i : USize) (pop : FloatArray) (hpop : nW.toNat < pop.size)
    (hpopU : pop.size < USize.size) (stale : Bool) :
    Gen20.applyU chs nW hchs ms lo hi hms hlo hhi i pop hpop stale =
      Gen18.applyW chs ms lo hi nW i pop stale :=
  applyU_eq chs nW hchs ms lo hi hms hlo hhi _ i rfl pop hpop hpopU stale

theorem smallU_eq' (chs : Array Gen18.ChangeW) (nW : USize)
    (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat) (pop : FloatArray)
    (hpop : nW.toNat < pop.size) (i : USize) :
    Gen20.smallU chs nW hchs pop hpop i = Gen18.smallFrom chs pop i :=
  smallU_eq chs nW hchs pop hpop _ i rfl

theorem refreshFromU_eq' (W : Gen18.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (nW numRx : USize) (rates : FloatArray) (hB : Gen20.Bounds W nW P numRx rates)
    (chs : Array Gen18.ChangeW)
    (hchs : ∀ k (h : k < chs.size), (chs[k]'h).species.toNat < nW.toNat)
    (pop : FloatArray) (hpop : nW.toNat < pop.size) (i : USize) (c : Gen19.CacheV)
    (hc : Gen20.Sized nW P c) :
    Gen20.refreshFromU W P hP2 D nW numRx rates hB chs hchs pop hpop i c hc =
      Gen19.refreshFromV W P P hP2 D chs pop i c :=
  refreshFromU_eq W P hP2 D nW numRx rates hB chs hchs pop hpop _ i rfl c hc

theorem ite_false_not (p : Prop) [Decidable p] (a : Bool) :
    (if p then a else false) = (if (!decide p) = true then false else a) := by
  by_cases h : p <;> simp [h]

theorem dite_ite_eq {c d : Prop} [Decidable c] [Decidable d] {α : Sort _} (h : c = d)
    {f : c → α} {g : ¬c → α} {x y : α} (hf : ∀ hc, f hc = x) (hg : ∀ hc, g hc = y) :
    dite c f g = ite d x y := by
  subst h
  by_cases hc : c
  · rw [dite_eq_left hc, ite_eq_left hc, hf]
  · rw [dite_eq_right hc, ite_eq_right hc, hg]

theorem run20_eq_of (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (horizon : Float) (save : Bool) (cap : USize)
    (fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3
      (count : USize) trace, evW.toNat = f →
      Gen20.run C codes W msN n hms hval nW numRx P hP2 D rates hB horizon save cap evW prW pop
          hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
      evW.toNat = fuel → prW.toNat = prFuel →
      Gen20.run C codes W msN n hms hval nW numRx P hP2 D rates hB horizon save cap evW prW pop
          hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have h0 : prW = 0 := USize.toNat_inj.mp (by rw [hpr]; rfl)
    rw [Gen20.run, dite_eq_left h0, Gen19.run, dite_eq_left h0]
  | succ pf ih =>
    intro evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev hpr
    have hT := tree_usize P hP2 c.tree hc.2.2
    have hU := hB.nU
    have hpopU : pop.size < USize.size := by omega
    have ih' : ∀ pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
        Gen20.run C codes W msN n hms hval nW numRx P hP2 D rates hB horizon save cap evW (prW - 1)
            pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
          Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW (prW - 1)
            pop c now total elapsed s0 s1 s2 s3 count trace :=
      fun pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
        ih evW (prW - 1) pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
          (usize_pred_toNat hpr)
    by_cases he : evW = 0
    · rw [Gen20.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_left he, descendW20_eq', uget_fget, auget_aget, evalU_eq, ih', dite_eq_ite,
        ite_false_not]
    · have hev0 : evW.toNat ≠ 0 := fun h0 => he (USize.toNat_inj.mp (by rw [h0]; rfl))
      obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hn' : ∀ (prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize) trace,
          Gen20.run C codes W msN n hms hval nW numRx P hP2 D rates hB horizon save cap (evW - 1)
              prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =
            Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap (evW - 1)
              prW pop c now total elapsed s0 s1 s2 s3 count trace :=
        fun prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace =>
          hnext f hf (evW - 1) prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace
            (by rw [Gen16.pred_toNat evW he]; omega)
      rw [Gen20.run, dite_eq_right (usize_ne_zero_of_toNat hpr), Gen19.run,
        dite_eq_right (usize_ne_zero_of_toNat hpr), dite_eq_left hT]
      simp only [dite_eq_right he, descendW20_eq', uget_fget, auget_aget, evalU_eq, ih', hn',
        applyU_eq' (hpopU := hpopU), smallU_eq', refreshFromU_eq', Gen18.cget,
        dite_eq_ite, ite_false_not]
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
      exact dite_ite_eq rfl (fun _ => rfl) (fun _ => rfl)

/-- Generation 20's driver returns what generation 19's returns. -/
theorem gen20_run_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Gen18.Compiled)
    (msN : Array Nat) (n : Nat) (hms : msN.size = n) (hval : Gen15.ValidChanges C n)
    (nW numRx P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray)
    (hB : Gen20.Bounds W nW P numRx rates) (horizon : Float) (save : Bool) (cap : USize) :
    ∀ fuel prFuel (evW prW : USize) pop hpop c hc now total elapsed s0 s1 s2 s3 (count : USize)
      trace, evW.toNat = fuel → prW.toNat = prFuel →
      Gen20.run C codes W msN n hms hval nW numRx P hP2 D rates hB horizon save cap evW prW pop
          hpop c hc now total elapsed s0 s1 s2 s3 count trace =
        Gen19.run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evW prW pop c
          now total elapsed s0 s1 s2 s3 count trace := by
  intro fuel
  induction fuel with
  | zero =>
    exact run20_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB horizon save cap 0
      (fun f h => absurd h (by omega))
  | succ f ih =>
    refine run20_eq_of C codes W msN n hms hval nW numRx P hP2 D rates hB horizon save cap (f + 1) ?_
    intro f' hf' evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev
    obtain rfl : f' = f := by omega
    exact ih prW.toNat evW prW pop hpop c hc now total elapsed s0 s1 s2 s3 count trace hev rfl

theorem start20_eq (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float)
    (save : Bool) (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (count : Nat) (trace : Array (Float × State)) :
    Gen20.start C codes horizon save cap fuel pop c now rng count trace =
      Gen19.start C codes horizon save cap fuel pop c now rng count trace := by
  unfold Gen20.start
  dsimp only
  split
  · rename_i h
    split
    · rename_i hs
      unfold Gen19.start
      have h1 : (!Gen7.finite (c.tree.get! 1)) = false := by rw [h.1]; rfl
      have h2 : (!decide (floatZero < c.tree.get! 1)) = false := by rw [h.2.1]; rfl
      simp only [h1, h2, Bool.false_eq_true, ite_false, dite_eq_left h.2.2, dite_eq_left hs.1]
      exact gen20_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        rfl rfl
    · rfl
  · rfl

/-- Generation 20 returns what generation 19 returns, on every network and input. -/
theorem gen20_eq_gen19 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen20.simulate net initial start horizon rng maxEvents save cap =
      Gen19.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen20.simulate Gen19.simulate
  simp only [start20_eq]

/-- **Generation 20 is the specification.** For every network whose reactant species are in
range and every input, generation 20 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen20_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen20.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen20_eq_gen19, gen19_simulate_eq net hwf]

end JumpProcessesLean.Proofs
