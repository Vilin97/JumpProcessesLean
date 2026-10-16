import FloatLib.Floats.Formats.IEEE754
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Semantics
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Subtraction
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics
import JumpProcessesLean.HostFloat

/-!
# Natural numbers as native floats

Below `2^53` a natural number `n` is a float exactly, `Float.ofNat n`. Sums, positive differences
and products below `2^53` of such floats are the floats of the integer results, comparisons agree
with the integers', and `Float.toUInt64` returns the integer. Generation 18 keeps its counts this
way. The proofs pass to FloatLib's model of binary64 through its bridges for Lean's native floats
(`ExecFloat.Binary.ofFloat`), where addition, subtraction and multiplication of finite values are
the exact real operation rounded once, and rounding a representable value returns it.
-/

namespace JumpProcessesLean.Proofs.Counts

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open Float.Model (UnpackedFloat)

/-- FloatLib's model of a native float. -/
abbrev fm (x : Float) : Model FloatFormat.binary64 := (ExecFloat.Binary.ofFloat x).toModel

theorem binary64_ieee : FloatFormat.binary64.isIEEE = true := by decide

theorem posMax_ge : (2 : ℝ) ^ 53 ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
  rw [Model.toReal_posMaxFinite]
  norm_num [FloatFormat.binary64, FloatFormat.maxNormalExponent, FloatFormat.maxFiniteFracField,
    Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal, Model.pow2,
    FloatFormat.fracMaskNat, FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent]
  have h2 : (2 : ℝ) ≤ 2 ^ 971 := le_self_pow₀ (by norm_num) (by norm_num)
  have h3 : (9007199254740991 : ℝ) * 2 ≤ 9007199254740991 * 2 ^ 971 :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  exact le_trans (by norm_num) h3

theorem posMax_ge' : (2 : ℝ) ^ 54 ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
  rw [Model.toReal_posMaxFinite]
  norm_num [FloatFormat.binary64, FloatFormat.maxNormalExponent, FloatFormat.maxFiniteFracField,
    Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal, Model.pow2,
    FloatFormat.fracMaskNat, FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent]
  have h2 : (4 : ℝ) ≤ 2 ^ 971 := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 971 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h3 : (9007199254740991 : ℝ) * 4 ≤ 9007199254740991 * 2 ^ 971 :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  exact le_trans (by norm_num) h3

/-- Below `2^53`, `Float.ofNat n` is finite with value `n`. -/
theorem ofNat_model (n : Nat) (hn : n < 2 ^ 53) :
    (fm (Float.ofNat n)).isFinite = true ∧ (fm (Float.ofNat n)).toReal = n := by
  have h := Model.roundDyadic_of_representable FloatFormat.binary64 binary64_ieee
    ⟨false, n, 0⟩ n 0 (by simp) (by simpa [FloatFormat.binary64] using hn)
    (show FloatFormat.binary64.minSubnormalExponent ≤ (0 : Int) by decide) (by
      have : ((⟨false, n, 0⟩ : FloatLib.Numerics.Dyadic).toReal) = n := by
        simp [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]
      rw [this, abs_of_nonneg (Nat.cast_nonneg n)]
      exact le_trans (by exact_mod_cast hn.le) posMax_ge)
  rw [fm, ExecFloat.Binary.toModel_ofFloat_ofNat,
    Model.roundRat_den_one_eq_roundDyadic _ binary64_ieee]
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The value of a native float is that of its unpacked model. -/
theorem toReal_fm (x : Float) : (fm x).toReal = Model.unpackedToReal x.toModel.unpack := by
  rw [fm, ExecFloat.Binary.toModel_ofFloat, Model.toReal_eq_unpackedToReal_toModel binary64_ieee,
    Model.toModel_ofFloatModel]

/-- Native floats with the same FloatLib model are equal. -/
theorem fm_inj {x y : Float} (h : fm x = fm y) : x = y := by
  have h1 : ExecFloat.Binary.ofFloat x = ExecFloat.Binary.ofFloat y :=
    Configured.Family.toModel_injective h
  rw [← ExecFloat.Binary.toFloat_ofFloat x, ← ExecFloat.Binary.toFloat_ofFloat y, h1]

/-! ## Unpacked forms -/

/-- Normalized mantissa–exponent pairs, as `unpack` produces them. -/
def Norm (m : Nat) (e : Int) : Prop := m < 2 ^ 53 ∧ -1074 ≤ e ∧ (-1074 < e → 2 ^ 52 ≤ m)

theorem unpack_finite_norm (b : BitVec 64) (s : UnpackedFloat.Sign) (m : Nat) (e : Int)
    (hm : 0 < m) (h : UnpackedFloat.unpack Float.Model.Format.binary64 b = .finite s m e hm) :
    Norm m e := by
  have hM := (UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).isLt
  have hE := (UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).isLt
  simp only [Float.Model.Format.binary64] at hM hE
  unfold UnpackedFloat.unpack at h
  by_cases h1 : UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = -1#_
  · simp only [h1, ↓reduceIte] at h
    split at h <;> cases h
  · by_cases h0 : UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b = 0#_
    · simp only [h0, ↓reduceIte] at h
      by_cases hz : UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b = 0#_
      · simp only [hz, ↓reduceDIte] at h; cases h
      · simp only [hz, ↓reduceDIte] at h
        injection h with hs hm' he
        subst hm' he
        refine ⟨by omega, ?_, ?_⟩
        · simp [Float.Model.Format.exponentBias]
        · intro hlt; simp [Float.Model.Format.exponentBias] at hlt
    · simp only [h1, h0, ↓reduceIte] at h
      injection h with hs hm' he
      subst hm' he
      have hne : (UnpackedFloat.unpackExponent (spec := Float.Model.Format.binary64) b).toNat ≠ 0 := by
        intro hz; exact h0 (BitVec.eq_of_toNat_eq (by simpa using hz))
      rw [BitVec.toNat_append]
      have hlo : 4503599627370496 ≤
          4503599627370496 ||| (UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat :=
        Nat.left_le_or
      have hhi : 4503599627370496 |||
          (UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat < 9007199254740992 := by
        have := Nat.or_lt_two_pow (show 4503599627370496 < 2 ^ 53 by norm_num)
          (show (UnpackedFloat.unpackMantissa (spec := Float.Model.Format.binary64) b).toNat < 2 ^ 53 by omega)
        simpa using this
      refine ⟨by simpa using hhi, ?_, ?_⟩
      · simp [Float.Model.Format.binary64, Float.Model.Format.exponentBias]; omega
      · intro _; simpa using hlo

theorem count_unpack_zero : (Float.ofNat 0).toModel.unpack = .zero .positive := by rfl

/-- A positive natural number below `2^53` unpacks to a positive normalized finite value. -/
theorem count_unpack_pos {a : Nat} (h0 : 0 < a) (h : a < 2 ^ 53) :
    ∃ m e hm, (Float.ofNat a).toModel.unpack = .finite .positive m e hm ∧ Norm m e ∧
      (m : ℝ) * (2 : ℝ) ^ e = a := by
  have hv : Model.unpackedToReal (Float.ofNat a).toModel.unpack = a := by
    rw [← toReal_fm]; exact (ofNat_model a h).2
  have ha : (0 : ℝ) < a := by exact_mod_cast h0
  generalize hu : (Float.ofNat a).toModel.unpack = u at hv
  cases u with
  | notANumber => simp [Model.unpackedToReal, Model.unpackedToDyadic?] at hv; linarith
  | infinity s => simp [Model.unpackedToReal, Model.unpackedToDyadic?] at hv; linarith
  | zero s => simp at hv; linarith
  | finite s m e hm =>
    have hn : Norm m e := unpack_finite_norm _ s m e hm hu
    cases s with
    | negative =>
      simp [Model.modelSignBit, Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
        FloatLib.Numerics.Radix.toReal] at hv
      have : (0 : ℝ) ≤ (m : ℝ) * 2 ^ e := by positivity
      linarith
    | positive =>
      refine ⟨m, e, hm, rfl, hn, ?_⟩
      simpa [Model.modelSignBit, Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
        FloatLib.Numerics.Radix.toReal] using hv


/-! ## Comparisons -/

theorem lex_lt_value {m1 m2 : Nat} {e1 e2 : Int} (h1 : Norm m1 e1) (h2 : Norm m2 e2)
    (h : e1 < e2 ∨ (e1 = e2 ∧ m1 < m2)) :
    (m1 : ℝ) * (2 : ℝ) ^ e1 < (m2 : ℝ) * (2 : ℝ) ^ e2 := by
  rcases h with he | ⟨he, hm⟩
  · have hm2 : 2 ^ 52 ≤ m2 := h2.2.2 (by have := h1.2.1; omega)
    have hm1 : (m1 : ℝ) < 2 ^ 53 := by exact_mod_cast h1.1
    have hm2' : (2 : ℝ) ^ 52 ≤ m2 := by exact_mod_cast hm2
    have hstep : (2 : ℝ) ^ (e1 + 1) ≤ (2 : ℝ) ^ e2 := zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc (m1 : ℝ) * (2 : ℝ) ^ e1 < (2 : ℝ) ^ 53 * (2 : ℝ) ^ e1 := by gcongr
      _ = (2 : ℝ) ^ 52 * (2 : ℝ) ^ (e1 + 1) := by
        rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring
      _ ≤ (m2 : ℝ) * (2 : ℝ) ^ e2 := by
        apply mul_le_mul hm2' hstep (by positivity) (by positivity)
  · subst he
    have hpos : (0 : ℝ) < (2 : ℝ) ^ e1 := zpow_pos (by norm_num) _
    have : (m1 : ℝ) < m2 := by exact_mod_cast hm
    nlinarith

/-- For normalized positive values, comparing exponents and then mantissas compares the values. -/
theorem lex_eq_compare {m1 m2 : Nat} {e1 e2 : Int} (h1 : Norm m1 e1) (h2 : Norm m2 e2) :
    (compare e1 e2).then (compare m1 m2) =
      compare ((m1 : ℝ) * (2 : ℝ) ^ e1) ((m2 : ℝ) * (2 : ℝ) ^ e2) := by
  rcases lt_trichotomy e1 e2 with he | he | he
  · rw [compare_lt_iff_lt.mpr he, compare_lt_iff_lt.mpr (lex_lt_value h1 h2 (Or.inl he))]; rfl
  · subst he
    rw [compare_eq_iff_eq.mpr rfl, Ordering.then]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ e1 := zpow_pos (by norm_num) _
    rcases lt_trichotomy m1 m2 with hm | hm | hm
    · rw [compare_lt_iff_lt.mpr hm, compare_lt_iff_lt.mpr (lex_lt_value h1 h2 (Or.inr ⟨rfl, hm⟩))]
    · subst hm; rw [compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
    · rw [compare_gt_iff_gt.mpr hm, compare_gt_iff_gt.mpr (lex_lt_value h2 h1 (Or.inr ⟨rfl, hm⟩))]
  · rw [compare_gt_iff_gt.mpr he, compare_gt_iff_gt.mpr (lex_lt_value h2 h1 (Or.inl he))]; rfl

theorem compare_cast (a b : Nat) : compare (a : ℝ) (b : ℝ) = compare a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (by exact_mod_cast h)]
  · subst h; rw [compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (by exact_mod_cast h)]

/-- Below `2^53` the floats of natural numbers compare as the numbers. -/
theorem count_compare {a b : Nat} (ha : a < 2 ^ 53) (hb : b < 2 ^ 53) :
    (Float.ofNat a).toModel.unpack.compare (Float.ofNat b).toModel.unpack = some (compare a b) := by
  rcases Nat.eq_zero_or_pos a with ha0 | ha0 <;> rcases Nat.eq_zero_or_pos b with hb0 | hb0
  · subst ha0 hb0; rw [count_unpack_zero]; rfl
  · subst ha0
    obtain ⟨m, e, hm, hu, -, -⟩ := count_unpack_pos hb0 hb
    rw [count_unpack_zero, hu, compare_lt_iff_lt.mpr hb0]; rfl
  · subst hb0
    obtain ⟨m, e, hm, hu, -, -⟩ := count_unpack_pos ha0 ha
    rw [count_unpack_zero, hu, compare_gt_iff_gt.mpr ha0]; rfl
  · obtain ⟨m1, e1, hm1, hu1, hn1, hv1⟩ := count_unpack_pos ha0 ha
    obtain ⟨m2, e2, hm2, hu2, hn2, hv2⟩ := count_unpack_pos hb0 hb
    rw [hu1, hu2]
    show some ((compare e1 e2).then (compare m1 m2)) = _
    rw [lex_eq_compare hn1 hn2, hv1, hv2, compare_cast]

theorem decide_lt (a b : Float) : decide (a < b) = a.toModel.unpack.lt b.toModel.unpack := by
  show decide (Float.lt a b = true) = _
  rw [Bool.decide_eq_true]
  unfold Float.lt
  show decide (a.toModel.lt b.toModel = true) = _
  rw [Bool.decide_eq_true]
  rfl

theorem decide_le (a b : Float) : decide (a ≤ b) = a.toModel.unpack.le b.toModel.unpack := by
  show decide (Float.le a b = true) = _
  rw [Bool.decide_eq_true]
  unfold Float.le
  show decide (a.toModel.le b.toModel = true) = _
  rw [Bool.decide_eq_true]
  rfl

theorem count_lt {a b : Nat} (ha : a < 2 ^ 53) (hb : b < 2 ^ 53) :
    decide (Float.ofNat a < Float.ofNat b) = decide (a < b) := by
  rw [decide_lt]
  show ((Float.ofNat a).toModel.unpack.compare (Float.ofNat b).toModel.unpack == some .lt) = _
  rw [count_compare ha hb]
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h]; simp [h]
  · subst h; rw [compare_eq_iff_eq.mpr rfl]; simp
  · rw [compare_gt_iff_gt.mpr h]; simp [Nat.not_lt.mpr h.le]

theorem count_le {a b : Nat} (ha : a < 2 ^ 53) (hb : b < 2 ^ 53) :
    decide (Float.ofNat a ≤ Float.ofNat b) = decide (a ≤ b) := by
  rw [decide_le]
  show ((Float.ofNat a).toModel.unpack.compare (Float.ofNat b).toModel.unpack).any (·.isLE) = _
  rw [count_compare ha hb]
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h]; simp [h.le]
  · subst h; rw [compare_eq_iff_eq.mpr rfl]; simp
  · rw [compare_gt_iff_gt.mpr h]; simp [Nat.not_le.mpr h]

theorem count_beq {a b : Nat} (ha : a < 2 ^ 53) (hb : b < 2 ^ 53) :
    (Float.ofNat a == Float.ofNat b) = (a == b) := by
  show ((Float.ofNat a).toModel.unpack.compare (Float.ofNat b).toModel.unpack == some .eq) = _
  rw [count_compare ha hb]
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h]; simp [h.ne]
  · subst h; rw [compare_eq_iff_eq.mpr rfl]; simp
  · rw [compare_gt_iff_gt.mpr h]; simp [h.ne']


/-! ## Arithmetic -/

theorem count_finite {a : Nat} (h : a < 2 ^ 53) : (Float.ofNat a).isFinite = true := by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0; rfl
  · obtain ⟨m, e, hm, hu, -⟩ := count_unpack_pos h0 h
    show (Float.ofNat a).toModel.unpack.isFinite = true
    rw [hu]; rfl

/-- A float whose model is finite with the value of a positive natural number is its float. -/
theorem count_eq_of_value {x : Float} {c : Nat} (hc : c < 2 ^ 53) (h0 : 0 < c)
    (hfin : (fm x).isFinite = true) (hv : (fm x).toReal = c) : x = Float.ofNat c := by
  apply fm_inj
  have hc' := ofNat_model c hc
  exact Model.eq_of_toReal_eq_of_nonzero hfin hc'.1 (by rw [hv, hc'.2])
    (by rw [hv]; exact_mod_cast h0.ne')

theorem count_add {a b : Nat} (h : a + b < 2 ^ 53) :
    Float.ofNat a + Float.ofNat b = Float.ofNat (a + b) := by
  rcases Nat.eq_zero_or_pos (a + b) with h0 | h0
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    rfl
  · have ha := ofNat_model a (by omega)
    have hb := ofNat_model b (by omega)
    have hsum : fm (Float.ofNat a + Float.ofNat b) =
        (fm (Float.ofNat a)).add (fm (Float.ofNat b)) :=
      ExecFloat.Binary.toModel_ofFloat_add_of_isFinite _ _ (count_finite (by omega))
        (count_finite (by omega))
    have hbound : |(fm (Float.ofNat a)).toReal| + |(fm (Float.ofNat b)).toReal| ≤
        (Model.posMaxFinite FloatFormat.binary64).toReal := by
      rw [ha.2, hb.2, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
      have : (a : ℝ) + b ≤ 2 ^ 53 := by exact_mod_cast h.le
      exact le_trans this posMax_ge
    have hfin := Model.isFinite_add_of_abs_add_le_posMaxFinite _ _ binary64_ieee ha.1 hb.1 hbound
    apply count_eq_of_value h h0 (by rw [hsum]; exact hfin)
    have hc := ofNat_model (a + b) h
    rw [hsum, Model.toReal_add_eq_roundAt _ _ binary64_ieee ha.1 hb.1 hfin, ha.2, hb.2,
      show ((a : ℝ) + b) = (fm (Float.ofNat (a + b))).toReal by rw [hc.2]; push_cast; ring,
      Model.roundAt_toReal_eq _ hc.1, hc.2]

/-- A positive difference of floats of natural numbers below `2^53` is exact. -/
theorem count_sub {a b : Nat} (hba : b < a) (h : a < 2 ^ 53) :
    Float.ofNat a - Float.ofNat b = Float.ofNat (a - b) := by
  have ha := ofNat_model a h
  have hb := ofNat_model b (by omega)
  have hdiff : fm (Float.ofNat a - Float.ofNat b) =
      (fm (Float.ofNat a)).sub (fm (Float.ofNat b)) :=
    ExecFloat.Binary.toModel_ofFloat_sub_of_isFinite _ _ (count_finite h) (count_finite (by omega))
  have hbound : |(fm (Float.ofNat a)).toReal| + |(fm (Float.ofNat b)).toReal| ≤
      (Model.posMaxFinite FloatFormat.binary64).toReal := by
    rw [ha.2, hb.2, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    have : (a : ℝ) + b ≤ 2 ^ 53 * 2 := by
      have h1 : (a : ℝ) ≤ 2 ^ 53 := by exact_mod_cast h.le
      have h2 : (b : ℝ) ≤ 2 ^ 53 := by exact_mod_cast (show b ≤ 2 ^ 53 by omega)
      linarith
    refine le_trans this (le_trans ?_ posMax_ge')
    norm_num
  have hfin := Model.isFinite_sub_of_abs_add_le_posMaxFinite _ _ binary64_ieee ha.1 hb.1 hbound
  apply count_eq_of_value (by omega) (by omega) (by rw [hdiff]; exact hfin)
  have hc := ofNat_model (a - b) (by omega)
  rw [hdiff, Model.toReal_sub_eq_roundAt _ _ binary64_ieee ha.1 hb.1 hfin, ha.2, hb.2,
    show ((a : ℝ) - b) = (fm (Float.ofNat (a - b))).toReal by rw [hc.2, Nat.cast_sub hba.le],
    Model.roundAt_toReal_eq _ hc.1, hc.2]


/-- A positive natural number's float is a normal number. -/
theorem count_normal {m : Nat} {e : Int} {c : Nat} (hn : Norm m e) (hc : 0 < c)
    (hv : (m : ℝ) * (2 : ℝ) ^ e = c) : 2 ^ 52 ≤ m := by
  apply hn.2.2
  by_contra hle
  push Not at hle
  have h1 : (2 : ℝ) ^ e ≤ (2 : ℝ) ^ (-1074 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
  have h2 : (m : ℝ) < 2 ^ 53 := by exact_mod_cast hn.1
  have h3 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have h4 : (2 : ℝ) ^ (53 : ℕ) * (2 : ℝ) ^ (-1074 : ℤ) < 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    exact zpow_lt_one_of_neg₀ (by norm_num) (by norm_num)
  have hp : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have : (m : ℝ) * (2 : ℝ) ^ e < 1 :=
    calc (m : ℝ) * (2 : ℝ) ^ e ≤ (m : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ ≤ (2 : ℝ) ^ (53 : ℕ) * (2 : ℝ) ^ (-1074 : ℤ) :=
          mul_le_mul_of_nonneg_right h2.le (zpow_nonneg (by norm_num) _)
      _ < 1 := h4
  linarith

theorem count_mul {a b : Nat} (ha : a < 2 ^ 53) (hb : b < 2 ^ 53) (h : a * b < 2 ^ 53) :
    Float.ofNat a * Float.ofNat b = Float.ofNat (a * b) := by
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0
    rw [Nat.zero_mul]
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0; rfl
    · obtain ⟨m, e, hm, hu, -⟩ := count_unpack_pos hb0 hb
      show Float.ofModel (Float.Model.pack (UnpackedFloat.mul _ (Float.ofNat 0).toModel.unpack
        (Float.ofNat b).toModel.unpack)) = Float.ofNat 0
      rw [count_unpack_zero, hu]
      rfl
  rcases Nat.eq_zero_or_pos b with hb0 | hb0
  · subst hb0
    rw [Nat.mul_zero]
    obtain ⟨m, e, hm, hu, -⟩ := count_unpack_pos ha0 ha
    show Float.ofModel (Float.Model.pack (UnpackedFloat.mul _ (Float.ofNat a).toModel.unpack
      (Float.ofNat 0).toModel.unpack)) = Float.ofNat 0
    rw [count_unpack_zero, hu]
    rfl
  obtain ⟨m1, e1, hm1, hu1, hn1, hv1⟩ := count_unpack_pos ha0 ha
  obtain ⟨m2, e2, hm2, hu2, hn2, hv2⟩ := count_unpack_pos hb0 hb
  have hm1' := count_normal hn1 ha0 hv1
  have hm2' := count_normal hn2 hb0 hv2
  have hab0 : 0 < a * b := Nat.mul_pos ha0 hb0
  have hfm : fm (Float.ofNat a * Float.ofNat b) =
      Model.ofModel FloatFormat.binary64
        (UnpackedFloat.mul (FloatFormat.toModel FloatFormat.binary64)
          (.finite .positive m1 e1 hm1) (.finite .positive m2 e2 hm2)) := by
    rw [fm, ExecFloat.Binary.toModel_ofFloat]
    show Model.ofFloatModel (Float.Model.pack (UnpackedFloat.mul _ (Float.ofNat a).toModel.unpack
      (Float.ofNat b).toModel.unpack)) = _
    rw [hu1, hu2]
    rfl
  have hlog : 52 ≤ (m1 * m2).log2 := by
    rw [Nat.le_log2 (Nat.mul_ne_zero hm1.ne' hm2.ne')]
    calc 2 ^ 52 ≤ 2 ^ 52 * 2 ^ 52 := Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ m1 * m2 := Nat.mul_le_mul hm1' hm2'
  have hle : e1 + e2 ≤ (FloatFormat.toModel FloatFormat.binary64).targetExponent
      (Float.Model.totalExponent (m1 * m2) (e1 + e2)) := by
    simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent]
    apply le_max_of_le_left
    show e1 + e2 ≤ ↑(m1 * m2).log2 + 1 + (e1 + e2) - 53
    omega
  have hval : ((m1 * m2 : Nat) : ℝ) * Formats.Flocq.bpow FloatLib.Numerics.binaryRadix (e1 + e2) =
      (a * b : Nat) := by
    simp only [Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
    push_cast
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← hv1, ← hv2]
    ring
  have hfin : (Model.ofModel FloatFormat.binary64
      (UnpackedFloat.mul (FloatFormat.toModel FloatFormat.binary64)
        (.finite .positive m1 e1 hm1) (.finite .positive m2 e2 hm2))).isFinite = true := by
    apply Model.isFinite_ofModel_roundWithAccuracy_of_lt_bpow FloatFormat.binary64 binary64_ieee
      _ (m1 * m2) (e1 + e2) .exact ((m1 * m2 : Nat) : ℝ) (Nat.mul_ne_zero hm1.ne' hm2.ne')
      (by simp [Model.accuracyRepresents]) hle
    rw [hval]
    have : ((a * b : Nat) : ℝ) < 2 ^ 53 := by exact_mod_cast h
    refine lt_of_lt_of_le this ?_
    simp only [Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
    have hk : 53 ≤ FloatFormat.ieeeMaxNormalExponent FloatFormat.binary64 := by decide
    rw [show Int.ofNat (FloatFormat.ieeeMaxNormalExponent FloatFormat.binary64) =
      ((FloatFormat.ieeeMaxNormalExponent FloatFormat.binary64 : ℕ) : ℤ) from rfl, zpow_natCast]
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hk
  apply count_eq_of_value h hab0 (by rw [hfm]; exact hfin)
  have hc := ofNat_model (a * b) h
  rw [hfm, Model.toReal_ofModel_mul_finite_eq_roundAt FloatFormat.binary64 binary64_ieee
    .positive .positive m1 m2 e1 e2 hm1 hm2 hle hfin]
  simp only [Model.unpackedToReal_finite]
  rw [show ((if Model.modelSignBit .positive then (-1 : ℝ) else 1) * (m1 : ℝ) *
        Formats.Flocq.bpow FloatLib.Numerics.binaryRadix e1 *
      ((if Model.modelSignBit .positive then (-1 : ℝ) else 1) * (m2 : ℝ) *
        Formats.Flocq.bpow FloatLib.Numerics.binaryRadix e2)) =
      (fm (Float.ofNat (a * b))).toReal by
    rw [hc.2]
    simp only [Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
    simp [Model.modelSignBit]
    rw [← hv1, ← hv2]]
  rw [Model.roundAt_toReal_eq _ hc.1, hc.2]


/-! ## Conversions -/

theorem repeat_shiftRightOne_mantissa (k : Nat) (em : UnpackedFloat.ExtendedMantissa) :
    (k.repeat UnpackedFloat.ExtendedMantissa.shiftRightOne em).mantissa = em.mantissa / 2 ^ k := by
  induction k with
  | zero => simp [Nat.repeat]
  | succ k ih =>
    simp only [Nat.repeat, UnpackedFloat.ExtendedMantissa.shiftRightOne, ih, Nat.pow_succ,
      Nat.div_div_eq_div_mul]

theorem shiftRight_mantissa (em : UnpackedFloat.ExtendedMantissa) (k : Nat) :
    (em >>> k).mantissa = em.mantissa / 2 ^ k :=
  repeat_shiftRightOne_mantissa k em

/-- Below `2^53`, truncating the float of a natural number returns it. -/
theorem count_toUInt64 {a : Nat} (ha : a < 2 ^ 53) : (Float.ofNat a).toUInt64 = a.toUInt64 := by
  show UnpackedFloat.toUInt64 (Float.ofNat a).toModel.unpack = _
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0; rw [count_unpack_zero]; rfl
  obtain ⟨m, e, hm, hu, hn, hv⟩ := count_unpack_pos h0 ha
  rw [hu]
  have key : UnpackedFloat.roundToInt .positive m e = (a : Int) := by
    unfold UnpackedFloat.roundToInt UnpackedFloat.decreaseExponent UnpackedFloat.shiftToExponent
    rcases le_or_gt 0 e with he | he
    · obtain ⟨k, rfl⟩ : ∃ k : Nat, e = k := ⟨e.toNat, by omega⟩
      have hmk : m * 2 ^ k = a := by
        have : (m : ℝ) * (2 : ℝ) ^ (k : ℤ) = a := hv
        rw [zpow_natCast] at this
        exact_mod_cast this
      simp only [shiftRight_mantissa]
      simp [UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy, UnpackedFloat.Sign.apply,
        Nat.shiftLeft_eq, hmk]
    · obtain ⟨k, hk⟩ : ∃ k : Nat, e = -(k : Int) := ⟨(-e).toNat, by omega⟩
      subst hk
      have hmk : m = a * 2 ^ k := by
        have : (m : ℝ) * (2 : ℝ) ^ (-(k : ℤ)) = a := hv
        rw [zpow_neg, zpow_natCast] at this
        have h2 : (0 : ℝ) < 2 ^ k := by positivity
        have : (m : ℝ) = a * 2 ^ k := by field_simp at this; linarith
        exact_mod_cast this
      have h1 : (-(k : Int) - 0).toNat = 0 := by omega
      have h2 : (0 - (-(k : Int) - ((0 : Nat) : Int))).toNat = k := by omega
      simp only [shiftRight_mantissa, h1, Nat.shiftLeft_zero, h2]
      simp [UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy, UnpackedFloat.Sign.apply, hmk]
  show UInt64.ofNatClamp ((UnpackedFloat.roundToInt .positive m e).toNat) = a.toUInt64
  rw [key, Int.toNat_natCast]
  have hs : a < UInt64.size := by simp [UInt64.size]; omega
  rw [UInt64.ofNatClamp, dif_pos hs]
  apply UInt64.toNat_inj.mp
  simp [Nat.toUInt64, UInt64.toNat_ofNat']
  omega

/-- `UInt64.toFloat` is `Float.ofNat` of the number. -/
theorem uint64_toFloat (u : UInt64) : u.toFloat = Float.ofNat u.toNat := by
  apply fm_inj
  rw [fm, fm, ExecFloat.Binary.toModel_ofFloat_ofNat, ExecFloat.Binary.toModel_ofFloat]
  show Model.ofFloatModel (Float.Model.pack
    (UnpackedFloat.ofInt Float.Model.Format.binary64 (u.toNat : Int))) = _
  rw [Model.ofFloatModel_pack]
  change Model.ofModel FloatFormat.binary64
    (UnpackedFloat.ofInt FloatFormat.binary64.toModel (u.toNat : Int)) = _
  rw [Model.ofModel_ofInt_eq_roundRat _ binary64_ieee]
  simp
  congr 1
  simp only [decide_eq_false_iff_not, not_lt]
  positivity

/-- `natToFloat` is `Float.ofNat`. -/
theorem natToFloat_eq (n : Nat) (h : n < 2 ^ 64) : natToFloat n = Float.ofNat n := by
  unfold natToFloat
  split
  · rw [uint64_toFloat]
    congr 1
    have h' : n < 18446744073709551616 := by simpa using h
    simp [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h']
  · rfl

theorem floatZero_eq : floatZero = Float.ofNat 0 := rfl
theorem floatOne_eq : floatOne = Float.ofNat 1 := rfl

end JumpProcessesLean.Proofs.Counts
