import JumpProcessesLean.Proofs.NativeCounts

/-!
# Order facts for native floats

`UnpackedFloat.compare` compares the infinities, the signs, then the exponents and the
mantissas lexicographically, so the native comparisons are transitive (`float_le_trans`,
`float_lt_of_lt_of_le`). FloatLib's finiteness of a native float is that of its unpacked value
(`isFinite_fm`). Multiplication by a rate `0 ≤ r < 2^52` is monotone on counts below `2^53`
(`mul_count_mono`): the product is the exact product rounded once, and rounding is monotone.
So a lower bound `r · a` with `a ≤ b` accepts only proposals that `r · b` accepts
(`squeeze_redundant`).
-/

namespace JumpProcessesLean.Proofs.Counts

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open Float.Model (UnpackedFloat)

/-- FloatLib's finiteness of a binary64 word is that of its unpacked value. -/
theorem isFinite_eq_toModel (x : Model FloatFormat.binary64) :
    x.isFinite = (Model.toModel x).isFinite := by
  have hencoding : FloatFormat.binary64.encoding = .ieee := rfl
  simp only [Model.isFinite, hencoding, Model.IEEE.isFinite]
  rw [← Model.unpackExponent_toNat]
  unfold Model.toModel UnpackedFloat.unpack
  by_cases h : UnpackedFloat.unpackExponent (spec := FloatFormat.toModel FloatFormat.binary64)
      (Model.toModelBits x) = -1#_
  · rw [if_pos h, h]
    split <;> simp [UnpackedFloat.isFinite] <;> decide
  · rw [if_neg h]
    have hne : (UnpackedFloat.unpackExponent (spec := FloatFormat.toModel FloatFormat.binary64)
        (Model.toModelBits x)).toNat ≠ FloatFormat.expAllOnesNat FloatFormat.binary64 := by
      intro h2
      apply h
      apply BitVec.eq_of_toNat_eq
      rw [h2]
      decide
    have hb : ((UnpackedFloat.unpackExponent (spec := FloatFormat.toModel FloatFormat.binary64)
        (Model.toModelBits x)).toNat != FloatFormat.expAllOnesNat FloatFormat.binary64) = true := by
      simpa [bne_iff_ne] using hne
    rw [hb]
    split
    · split <;> rfl
    · rfl

theorem isFinite_fm (x : Float) : (fm x).isFinite = x.toModel.unpack.isFinite := by
  rw [isFinite_eq_toModel, fm, ExecFloat.Binary.toModel_ofFloat, Model.toModel_ofFloatModel]

/-! ## Transitivity -/

theorem then_isLE (e1 e2 : Int) (m1 m2 : Nat) :
    ((compare e1 e2).then (compare m1 m2)).isLE = decide (e1 < e2 ∨ (e1 = e2 ∧ m1 ≤ m2)) := by
  rcases lt_trichotomy e1 e2 with h | rfl | h
  · rw [compare_lt_iff_lt.mpr h]; simp [Ordering.then, h]
  · rw [compare_eq_iff_eq.mpr rfl]
    rcases lt_trichotomy m1 m2 with hm | rfl | hm
    · rw [compare_lt_iff_lt.mpr hm]; simp [Ordering.then, hm.le]
    · simp [Ordering.then]
    · rw [compare_gt_iff_gt.mpr hm]; simp [Ordering.then]; omega
  · rw [compare_gt_iff_gt.mpr h]; simp [Ordering.then]; omega

theorem then_isGE (e1 e2 : Int) (m1 m2 : Nat) :
    ((compare e1 e2).then (compare m1 m2)).isGE = decide (e2 < e1 ∨ (e1 = e2 ∧ m2 ≤ m1)) := by
  rcases lt_trichotomy e1 e2 with h | rfl | h
  · rw [compare_lt_iff_lt.mpr h]; simp [Ordering.then]; omega
  · rw [compare_eq_iff_eq.mpr rfl]
    rcases lt_trichotomy m1 m2 with hm | rfl | hm
    · rw [compare_lt_iff_lt.mpr hm]; simp [Ordering.then]; omega
    · simp [Ordering.then]
    · rw [compare_gt_iff_gt.mpr hm]; simp [Ordering.then, hm.le]
  · rw [compare_gt_iff_gt.mpr h]; simp [Ordering.then, h]

theorem sign_np : compare UnpackedFloat.Sign.negative UnpackedFloat.Sign.positive = .lt := by decide
theorem sign_pn : compare UnpackedFloat.Sign.positive UnpackedFloat.Sign.negative = .gt := by decide
theorem sign_nn : compare UnpackedFloat.Sign.negative UnpackedFloat.Sign.negative = .eq := by decide
theorem sign_pp : compare UnpackedFloat.Sign.positive UnpackedFloat.Sign.positive = .eq := by decide

/-- The model's `≤` is transitive. -/
theorem unpacked_le_trans (a b c : UnpackedFloat) (h1 : a.le b = true) (h2 : b.le c = true) :
    a.le c = true := by
  rcases a with ⟨⟨⟩ | ⟨⟩⟩ | _ | ⟨⟨⟩ | ⟨⟩⟩ | ⟨⟨⟩ | ⟨⟩, m1, e1, p1⟩ <;>
  rcases b with ⟨⟨⟩ | ⟨⟩⟩ | _ | ⟨⟨⟩ | ⟨⟩⟩ | ⟨⟨⟩ | ⟨⟩, m2, e2, p2⟩ <;>
  rcases c with ⟨⟨⟩ | ⟨⟩⟩ | _ | ⟨⟨⟩ | ⟨⟩⟩ | ⟨⟨⟩ | ⟨⟩, m3, e3, p3⟩ <;>
  simp_all [UnpackedFloat.le, UnpackedFloat.compare, then_isLE, then_isGE, sign_np, sign_pn,
    sign_nn, sign_pp] <;> omega

theorem then_eq_lt_iff (e1 e2 : Int) (m1 m2 : Nat) :
    (compare e1 e2).then (compare m1 m2) = .lt ↔ (e1 < e2 ∨ (e1 = e2 ∧ m1 < m2)) := by
  rcases lt_trichotomy e1 e2 with h | rfl | h
  · rw [compare_lt_iff_lt.mpr h]; simp [Ordering.then, h]
  · rw [compare_eq_iff_eq.mpr rfl]
    rcases lt_trichotomy m1 m2 with hm | rfl | hm
    · rw [compare_lt_iff_lt.mpr hm]; simp [Ordering.then, hm]
    · simp [Ordering.then]
    · rw [compare_gt_iff_gt.mpr hm]; simp [Ordering.then]; omega
  · rw [compare_gt_iff_gt.mpr h]; simp [Ordering.then]; omega

theorem then_eq_gt_iff (e1 e2 : Int) (m1 m2 : Nat) :
    (compare e1 e2).then (compare m1 m2) = .gt ↔ (e2 < e1 ∨ (e1 = e2 ∧ m2 < m1)) := by
  rcases lt_trichotomy e1 e2 with h | rfl | h
  · rw [compare_lt_iff_lt.mpr h]; simp [Ordering.then]; omega
  · rw [compare_eq_iff_eq.mpr rfl]
    rcases lt_trichotomy m1 m2 with hm | rfl | hm
    · rw [compare_lt_iff_lt.mpr hm]; simp [Ordering.then]; omega
    · simp [Ordering.then]
    · rw [compare_gt_iff_gt.mpr hm]; simp [Ordering.then, hm]
  · rw [compare_gt_iff_gt.mpr h]; simp [Ordering.then, h]

/-- The model's `<` followed by `≤` is `<`. -/
theorem unpacked_lt_of_lt_of_le (a b c : UnpackedFloat) (h1 : a.lt b = true) (h2 : b.le c = true) :
    a.lt c = true := by
  rcases a with ⟨⟨⟩ | ⟨⟩⟩ | _ | ⟨⟨⟩ | ⟨⟩⟩ | ⟨⟨⟩ | ⟨⟩, m1, e1, p1⟩ <;>
  rcases b with ⟨⟨⟩ | ⟨⟩⟩ | _ | ⟨⟨⟩ | ⟨⟩⟩ | ⟨⟨⟩ | ⟨⟩, m2, e2, p2⟩ <;>
  rcases c with ⟨⟨⟩ | ⟨⟩⟩ | _ | ⟨⟨⟩ | ⟨⟩⟩ | ⟨⟨⟩ | ⟨⟩, m3, e3, p3⟩ <;>
  simp_all [UnpackedFloat.lt, UnpackedFloat.le, UnpackedFloat.compare, then_isLE, then_isGE,
    then_eq_lt_iff, then_eq_gt_iff, sign_np, sign_pn, sign_nn, sign_pp] <;> omega

theorem float_le_trans {x y z : Float} (h1 : decide (x ≤ y) = true) (h2 : decide (y ≤ z) = true) :
    decide (x ≤ z) = true := by
  rw [decide_le] at *; exact unpacked_le_trans _ _ _ h1 h2

theorem float_lt_of_lt_of_le {x y z : Float} (h1 : decide (x < y) = true)
    (h2 : decide (y ≤ z) = true) : decide (x < z) = true := by
  rw [decide_lt] at *; rw [decide_le] at h2; exact unpacked_lt_of_lt_of_le _ _ _ h1 h2

/-! ## Monotone products -/

theorem unpackedToReal_pos (m : Nat) (e : Int) (hm : 0 < m) :
    Model.unpackedToReal (.finite .positive m e hm) = (m : ℝ) * (2 : ℝ) ^ e := by
  simp [Model.modelSignBit, Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
    FloatLib.Numerics.Radix.toReal]

theorem unpackedToReal_neg (m : Nat) (e : Int) (hm : 0 < m) :
    Model.unpackedToReal (.finite .negative m e hm) = -((m : ℝ) * (2 : ℝ) ^ e) := by
  simp [Model.modelSignBit, Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
    FloatLib.Numerics.Radix.toReal]

/-- The product of a positive finite float and a positive count below `2^53`, with value below
`2^1024`: finite, rounded once. -/
theorem mul_count_model {r : Float} {m0 : Nat} {e0 : Int} {hm0 : 0 < m0}
    (hr : r.toModel.unpack = .finite .positive m0 e0 hm0) (hrv : (m0 : ℝ) * (2 : ℝ) ^ e0 < 2 ^ 52)
    {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 53) :
    (fm (r * Float.ofNat a)).isFinite = true ∧
      (fm (r * Float.ofNat a)).toReal = Model.roundAt FloatFormat.binary64 ((m0 : ℝ) * (2 : ℝ) ^ e0 * a) := by
  obtain ⟨m1, e1, hm1, hu1, hn1, hv1⟩ := count_unpack_pos ha0 ha
  have hm1' := count_normal hn1 ha0 hv1
  have hfm : fm (r * Float.ofNat a) =
      Model.ofModel FloatFormat.binary64
        (UnpackedFloat.mul (FloatFormat.toModel FloatFormat.binary64)
          (.finite .positive m0 e0 hm0) (.finite .positive m1 e1 hm1)) := by
    rw [fm, ExecFloat.Binary.toModel_ofFloat]
    show Model.ofFloatModel (Float.Model.pack (UnpackedFloat.mul _ r.toModel.unpack
      (Float.ofNat a).toModel.unpack)) = _
    rw [hr, hu1]
    rfl
  have hlog : 52 ≤ (m0 * m1).log2 := by
    rw [Nat.le_log2 (Nat.mul_ne_zero hm0.ne' hm1.ne')]
    calc 2 ^ 52 ≤ m1 := hm1'
      _ ≤ m0 * m1 := Nat.le_mul_of_pos_left _ hm0
  have hle : e0 + e1 ≤ (FloatFormat.toModel FloatFormat.binary64).targetExponent
      (Float.Model.totalExponent (m0 * m1) (e0 + e1)) := by
    simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent]
    apply le_max_of_le_left
    show e0 + e1 ≤ ↑(m0 * m1).log2 + 1 + (e0 + e1) - 53
    omega
  have hval : ((m0 * m1 : Nat) : ℝ) * Formats.Flocq.bpow FloatLib.Numerics.binaryRadix (e0 + e1) =
      (m0 : ℝ) * (2 : ℝ) ^ e0 * a := by
    simp only [Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
    push_cast
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← hv1]
    ring
  have hfin : (Model.ofModel FloatFormat.binary64
      (UnpackedFloat.mul (FloatFormat.toModel FloatFormat.binary64)
        (.finite .positive m0 e0 hm0) (.finite .positive m1 e1 hm1))).isFinite = true := by
    apply Model.isFinite_ofModel_roundWithAccuracy_of_lt_bpow FloatFormat.binary64 binary64_ieee
      _ (m0 * m1) (e0 + e1) .exact ((m0 * m1 : Nat) : ℝ) (Nat.mul_ne_zero hm0.ne' hm1.ne')
      (by simp [Model.accuracyRepresents]) hle
    rw [hval]
    have ha' : (a : ℝ) < 2 ^ 53 := by exact_mod_cast ha
    have h0 : (0 : ℝ) ≤ (m0 : ℝ) * (2 : ℝ) ^ e0 := by positivity
    have : (m0 : ℝ) * (2 : ℝ) ^ e0 * a < 2 ^ 52 * 2 ^ 53 := by
      calc (m0 : ℝ) * (2 : ℝ) ^ e0 * a ≤ (m0 : ℝ) * (2 : ℝ) ^ e0 * 2 ^ 53 :=
            mul_le_mul_of_nonneg_left ha'.le h0
        _ < 2 ^ 52 * 2 ^ 53 := by
            apply mul_lt_mul_of_pos_right hrv (by positivity)
    refine lt_of_lt_of_le this ?_
    simp only [Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
    have hk : 105 ≤ FloatFormat.ieeeMaxNormalExponent FloatFormat.binary64 := by decide
    rw [show Int.ofNat (FloatFormat.ieeeMaxNormalExponent FloatFormat.binary64) =
      ((FloatFormat.ieeeMaxNormalExponent FloatFormat.binary64 : ℕ) : ℤ) from rfl, zpow_natCast]
    calc (2 : ℝ) ^ 52 * 2 ^ 53 = 2 ^ 105 := by norm_num
      _ ≤ 2 ^ FloatFormat.ieeeMaxNormalExponent FloatFormat.binary64 :=
          pow_le_pow_right₀ (by norm_num) hk
  refine ⟨by rw [hfm]; exact hfin, ?_⟩
  rw [hfm, Model.toReal_ofModel_mul_finite_eq_roundAt FloatFormat.binary64 binary64_ieee
    .positive .positive m0 m1 e0 e1 hm0 hm1 hle hfin]
  congr 1
  simp only [Model.unpackedToReal_finite]
  rw [← hval]
  simp only [Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
  simp [Model.modelSignBit]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem pack_zero_unpack (s : UnpackedFloat.Sign) :
    (Float.Model.pack (UnpackedFloat.zero s)).unpack = .zero s := by
  cases s <;> rfl

/-- A product with a zero factor and a finite or zero factor is zero. -/
theorem mul_zero_left_unpack (s : UnpackedFloat.Sign) (x : Float)
    (hx : x.toModel.unpack.isFinite = true) :
    ∃ s', (Float.Model.pack (UnpackedFloat.mul Float.Model.Format.binary64 (.zero s)
      x.toModel.unpack)).unpack = .zero s' := by
  generalize x.toModel.unpack = u at hx
  cases u with
  | infinity => simp [UnpackedFloat.isFinite] at hx
  | notANumber => simp [UnpackedFloat.isFinite] at hx
  | zero s2 => exact ⟨s * s2, pack_zero_unpack _⟩
  | finite s2 m e h => exact ⟨s * s2, pack_zero_unpack _⟩

/-- For a rate `0 ≤ r < 2^52` and counts `a ≤ b < 2^53`, a positive `r · a` is at most `r · b`. -/
theorem mul_count_mono {r : Float} (hr0 : decide (floatZero ≤ r) = true)
    (hr1 : decide (r < Float.ofNat (2 ^ 52)) = true) {a b : Nat} (hab : a ≤ b) (hb : b < 2 ^ 53)
    (hpos : decide (floatZero < r * Float.ofNat a) = true) :
    decide (r * Float.ofNat a ≤ r * Float.ofNat b) = true := by
  rw [floatZero_eq, decide_le, count_unpack_zero] at hr0
  rw [floatZero_eq, decide_lt, count_unpack_zero] at hpos
  rw [decide_lt] at hr1
  obtain ⟨mq, eq, hmq, huq, hnq, hvq⟩ :=
    count_unpack_pos (show 0 < 2 ^ 52 by norm_num) (by norm_num : 2 ^ 52 < 2 ^ 53)
  rw [huq] at hr1
  have hmul : ∀ c : Nat, (r * Float.ofNat c).toModel.unpack =
      (Float.Model.pack (UnpackedFloat.mul Float.Model.Format.binary64 r.toModel.unpack
        (Float.ofNat c).toModel.unpack)).unpack := fun c => rfl
  rcases hu : r.toModel.unpack with s0 | _ | s0 | ⟨s0, m0, e0, hm0⟩
  · rw [hu] at hr0 hr1; cases s0 <;> simp_all [UnpackedFloat.le, UnpackedFloat.lt, UnpackedFloat.compare]
  · rw [hu] at hr0; simp [UnpackedFloat.le, UnpackedFloat.compare] at hr0
  · rw [hmul, hu] at hpos
    obtain ⟨s', hs'⟩ := mul_zero_left_unpack s0 (Float.ofNat a) (count_finite (by omega))
    rw [hs'] at hpos
    simp [UnpackedFloat.lt, UnpackedFloat.compare] at hpos
  · cases s0 with
    | negative => rw [hu] at hr0; simp [UnpackedFloat.le, UnpackedFloat.compare] at hr0
    | positive =>
      have hn0 : Norm m0 e0 := unpack_finite_norm _ _ m0 e0 hm0 hu
      have hrv : (m0 : ℝ) * (2 : ℝ) ^ e0 < 2 ^ 52 := by
        rw [hu] at hr1
        have hlex : e0 < eq ∨ (e0 = eq ∧ m0 < mq) := by
          simpa [UnpackedFloat.lt, UnpackedFloat.compare, then_eq_lt_iff] using hr1
        have := lex_lt_value hn0 hnq hlex
        rw [hvq] at this
        exact_mod_cast this
      rcases Nat.eq_zero_or_pos a with ha0 | ha0
      · subst ha0
        rw [hmul, hu, count_unpack_zero] at hpos
        simp [UnpackedFloat.mul, pack_zero_unpack, UnpackedFloat.lt, UnpackedFloat.compare] at hpos
      have hL := mul_count_model hu hrv ha0 (by omega)
      have hA := mul_count_model hu hrv (show 0 < b by omega) hb
      have hmono : (fm (r * Float.ofNat a)).toReal ≤ (fm (r * Float.ofNat b)).toReal := by
        rw [hL.2, hA.2]
        apply Model.roundAt_mono
        have : (a : ℝ) ≤ b := by exact_mod_cast hab
        have h0 : (0 : ℝ) ≤ (m0 : ℝ) * (2 : ℝ) ^ e0 := by positivity
        exact mul_le_mul_of_nonneg_left this h0
      have hLf := hL.1
      have hAf := hA.1
      rw [isFinite_fm] at hLf hAf
      rw [toReal_fm, toReal_fm] at hmono
      rw [decide_le]
      generalize hL' : (r * Float.ofNat a).toModel.unpack = L at hpos hLf hmono
      generalize hA' : (r * Float.ofNat b).toModel.unpack = A at hAf hmono
      rcases L with sL | _ | sL | ⟨sL, m3, e3, hm3⟩
      · simp [UnpackedFloat.isFinite] at hLf
      · simp [UnpackedFloat.lt, UnpackedFloat.compare] at hpos
      · simp [UnpackedFloat.lt, UnpackedFloat.compare] at hpos
      · cases sL with
        | negative => simp [UnpackedFloat.lt, UnpackedFloat.compare] at hpos
        | positive =>
          have hn3 : Norm m3 e3 := unpack_finite_norm _ _ m3 e3 hm3 hL'
          rw [unpackedToReal_pos] at hmono
          have hp3 : (0 : ℝ) < (m3 : ℝ) * (2 : ℝ) ^ e3 := by
            have : (0 : ℝ) < m3 := by exact_mod_cast hm3
            positivity
          rcases A with sA | _ | sA | ⟨sA, m4, e4, hm4⟩
          · simp [UnpackedFloat.isFinite] at hAf
          · simp [UnpackedFloat.isFinite] at hAf
          · simp at hmono; linarith
          · cases sA with
            | negative =>
              rw [unpackedToReal_neg] at hmono
              have : (0 : ℝ) ≤ (m4 : ℝ) * (2 : ℝ) ^ e4 := by positivity
              linarith
            | positive =>
              have hn4 : Norm m4 e4 := unpack_finite_norm _ _ m4 e4 hm4 hA'
              rw [unpackedToReal_pos] at hmono
              show ((compare e3 e4).then (compare m3 m4)).isLE = true
              rw [lex_eq_compare hn3 hn4]
              rcases lt_or_eq_of_le hmono with h | h
              · rw [compare_lt_iff_lt.mpr h]; rfl
              · rw [h, compare_eq_iff_eq.mpr rfl]; rfl

/-- For a rate `0 ≤ r < 2^52` and counts `a ≤ b < 2^53`, a test that accepts when `r · a` is
positive and at least `t`, and otherwise tests `r · b`, is the test of `r · b`. -/
theorem squeeze_redundant {r t : Float} (hr0 : decide (floatZero ≤ r) = true)
    (hr1 : decide (r < Float.ofNat (2 ^ 52)) = true) {a b : Nat} (hab : a ≤ b) (hb : b < 2 ^ 53) :
    (if (decide (floatZero < r * Float.ofNat a) && decide (t ≤ r * Float.ofNat a)) = true then true
     else decide (floatZero < r * Float.ofNat b) && decide (t ≤ r * Float.ofNat b)) =
      (decide (floatZero < r * Float.ofNat b) && decide (t ≤ r * Float.ofNat b)) := by
  by_cases h : (decide (floatZero < r * Float.ofNat a) && decide (t ≤ r * Float.ofNat a)) = true
  · rw [if_pos h]
    rw [Bool.and_eq_true] at h
    have hle := mul_count_mono hr0 hr1 hab hb h.1
    rw [float_lt_of_lt_of_le h.1 hle, float_le_trans h.2 hle]
    rfl
  · rw [if_neg h]

end JumpProcessesLean.Proofs.Counts
