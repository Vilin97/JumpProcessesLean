import JumpProcessesLean.Proofs.FloatApproximation
import JumpProcessesLean.Proofs.OperationalNRM

namespace JumpProcessesLean.Proofs
set_option maxHeartbeats 1000000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma floatReal_zero : floatReal (0 : Binary64) = 0 := by
  change Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.ofModel (Model.zero FloatFormat.binary64 false))) = 0
  rw [ExecFloat.Binary.toModel_ofModel]
  exact Model.toReal_zero _ _

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma float_zero_finite : ExecFloat.Binary.isFinite (0 : Binary64) = true := by
  change Model.isFinite (ExecFloat.Binary.toModel (ExecFloat.Binary.ofModel (Model.zero FloatFormat.binary64 false))) = true
  rw [ExecFloat.Binary.toModel_ofModel]
  rfl

lemma nrmNextAux_time_mem {α : Type} (op : Arithmetic α) (clocks : List α) (k : Nat) (e : Event α)
    (he : nrmNextAux op (clocks.map some) k = some e) : e.time ∈ clocks := by
  induction clocks generalizing k e with
  | nil => simp [nrmNextAux] at he
  | cons a rest ih =>
    simp only [List.map_cons, nrmNextAux] at he
    cases h : nrmNextAux op (rest.map some) (k + 1) with
    | none => simp only [h] at he; cases he; simp
    | some b =>
      simp only [h] at he
      split at he
      · cases he; simp
      · cases he; exact List.mem_cons_of_mem _ (ih _ _ h)

/-- IEEE comparisons on finite clocks exactly refine real comparisons on decoded clocks. -/
theorem nrmNextAux_float_decode (clocks : List Binary64)
    (hf : ∀ c ∈ clocks, ExecFloat.Binary.isFinite c = true) (k : Nat) :
    (nrmNextAux binary64Arithmetic (clocks.map some) k).map
      (fun e => (⟨floatReal e.time, e.reaction⟩ : Event ℝ)) =
    nrmNextAux realArithmetic ((clocks.map floatReal).map some) k := by
  induction clocks generalizing k with
  | nil => rfl
  | cons a rest ih =>
    have ha := hf a (by simp)
    have hr := ih (fun c hc => hf c (by simp [hc])) (k + 1)
    cases h : nrmNextAux binary64Arithmetic (rest.map some) (k + 1) with
    | none =>
      simp only [h, Option.map_none] at hr
      simp only [List.map_cons, nrmNextAux, h, ← hr, Option.map_some]
    | some b =>
      have hb := hf b.time (List.mem_cons_of_mem _ (nrmNextAux_time_mem _ _ _ _ h))
      have hle := float_le_real a b.time ha hb
      have hcomp : binary64Arithmetic.le a b.time = realArithmetic.le (floatReal a) (floatReal b.time) := by
        simp only [binary64Arithmetic, realArithmetic]
        exact decide_eq_decide.mpr hle
      simp only [h, Option.map_some] at hr
      simp only [List.map_cons, nrmNextAux, h, ← hr, hcomp]
      split <;> rfl

/-- The actual FloatLib NRM selector preserves the mark, with a numerical time bound,
provided every clock error is bounded and the exact race gap exceeds twice that bound. -/
theorem nrm_float_winner_approx {n : Nat} (rates cf : Fin (n + 1) → Binary64)
    (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (η : ℝ)
    (hf : ∀ j, ExecFloat.Binary.isFinite (cf j) = true)
    (herr : ∀ j, |floatReal (cf j) - c j| ≤ η)
    (hgap : ∀ j, j ≠ i → c i + 2 * η < c j) :
    nrmNext binary64Arithmetic ⟨Array.ofFn rates, Array.ofFn (fun j => some (cf j))⟩ =
      some ⟨cf i, i.val⟩ ∧ |floatReal (cf i) - c i| ≤ η := by
  have hmin := race_margin_stable c (fun j => floatReal (cf j)) η i herr hgap
  have he := nrmNext_vector_unique (fun j => floatReal (rates j)) (fun j => floatReal (cf j)) i hmin
  have hd := nrmNextAux_float_decode (List.ofFn cf) (by
    intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha; exact hf j) 0
  simp only [nrmNext, Array.toList_ofFn, List.map_ofFn, Function.comp_def] at he hd ⊢
  rw [he] at hd
  constructor
  · cases h : nrmNextAux binary64Arithmetic (List.ofFn (fun j => some (cf j))) 0 with
    | none => simp only [h, Option.map_none, reduceCtorEq] at hd
    | some e =>
      simp only [h, Option.map_some, Option.some.injEq] at hd
      have hrx : e.reaction = i.val := congrArg Event.reaction hd
      have htime := nrmNextAux_time_mem binary64Arithmetic (List.ofFn cf) 0 e (by
        simpa only [List.map_ofFn, Function.comp_def] using h)
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp htime
      have hjtime : floatReal (cf j) = floatReal (cf i) := by
        simpa only [hj] using congrArg Event.time hd
      have hji : j = i := by
        by_contra hji
        exact (ne_of_lt (hmin j hji)) hjtime.symm
      have heq : e = ⟨cf i, i.val⟩ := by
        cases e
        simp_all
      simpa only [heq] using h
  · exact herr i

/-- The FloatLib RSSA comparison, including its lower-bound shortcut, refines the decoded
real comparison when the validated bounds enclose a strictly positive propensity. -/
theorem rssa_float_accept_decode (lower actual threshold : Binary64)
    (hl : ExecFloat.Binary.isFinite lower = true)
    (ha : ExecFloat.Binary.isFinite actual = true)
    (ht : ExecFloat.Binary.isFinite threshold = true)
    (hla : floatReal lower ≤ floatReal actual) :
    rssaAccept binary64Arithmetic lower actual threshold =
      decide (0 < floatReal actual ∧ floatReal threshold ≤ floatReal actual) := by
  have hlo := float_lt_real 0 lower float_zero_finite hl
  have hao := float_lt_real 0 actual float_zero_finite ha
  have htl := float_le_real threshold lower ht hl
  have hta := float_le_real threshold actual ht ha
  simp only [floatReal_zero] at hlo hao
  have hd : rssaAccept binary64Arithmetic lower actual threshold =
      rssaAccept realArithmetic (floatReal lower) (floatReal actual) (floatReal threshold) := by
    change ((decide (0 < lower) && decide (threshold ≤ lower)) ||
      (decide (0 < actual) && decide (threshold ≤ actual))) =
      ((decide (0 < floatReal lower) && decide (floatReal threshold ≤ floatReal lower)) ||
        (decide (0 < floatReal actual) && decide (floatReal threshold ≤ floatReal actual)))
    rw [decide_eq_decide.mpr hlo, decide_eq_decide.mpr hao,
      decide_eq_decide.mpr htl, decide_eq_decide.mpr hta]
  rw [hd, rssa_lower_shortcut _ _ _ hla]

theorem rssa_float_accept_stable (lower actual threshold : Binary64) (a v η : ℝ)
    (hl : ExecFloat.Binary.isFinite lower = true)
    (ha : ExecFloat.Binary.isFinite actual = true)
    (ht : ExecFloat.Binary.isFinite threshold = true)
    (hla : floatReal lower ≤ floatReal actual) (hap : 0 < floatReal actual) (ha0 : 0 < a)
    (hea : |floatReal actual - a| ≤ η) (hev : |floatReal threshold - v| ≤ η)
    (hgap : 2 * η < |v - a|) :
    rssaAccept binary64Arithmetic lower actual threshold = decide (v ≤ a) := by
  rw [rssa_float_accept_decode lower actual threshold hl ha ht hla]
  have hc := rejection_margin_stable v a (floatReal threshold) (floatReal actual) η hev hea hgap
  simp only [hap, true_and]
  exact decide_eq_decide.mpr hc

lemma foldFinite_take (acc : Binary64) (xs : List Binary64) (h : FoldFinite acc xs) (n : Nat) :
    FoldFinite acc (xs.take n) := by
  induction n generalizing acc xs with
  | zero => simpa only [List.take_zero, FoldFinite] using foldFinite_head acc xs h
  | succ n ih =>
    cases xs with
    | nil => exact h
    | cons x xs => exact ⟨h.1, h.2.1, ih (acc + x) xs h.2.2⟩

/-- A trace of finite IEEE comparisons refines the concrete real cumulative selector. -/
theorem chooseAux_float_compare_trace (weights : List Binary64) (cf xf : Binary64) (cr xr : ℝ)
    (hf : FoldFinite cf weights) (hx : ExecFloat.Binary.isFinite xf = true)
    (hc : ∀ (j : Nat) (hj : j < weights.length),
      xr < cr + ((weights.take (j + 1)).map floatReal).sum ↔
        floatReal xf < floatReal ((weights.take (j + 1)).foldl (· + ·) cf)) (index : Nat) :
    chooseAux binary64Arithmetic xf weights cf index =
      chooseAux realArithmetic xr (weights.map floatReal) cr index := by
  induction weights generalizing cf cr index with
  | nil => rfl
  | cons a rest ih =>
    have hn := foldFinite_head (cf + a) rest hf.2.2
    have hs := float_lt_real 0 a float_zero_finite hf.2.1
    simp only [floatReal_zero] at hs
    have ht := float_lt_real xf (cf + a) hx hn
    have hc0 := hc 0 (by simp)
    simp only [zero_add, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, List.foldl_cons, List.foldl_nil] at hc0
    have htest : (binary64Arithmetic.lt binary64Arithmetic.zero a &&
        binary64Arithmetic.lt xf (binary64Arithmetic.add cf a)) =
        (realArithmetic.lt realArithmetic.zero (floatReal a) &&
          realArithmetic.lt xr (realArithmetic.add cr (floatReal a))) := by
      change (decide (0 < a) && decide (xf < cf + a)) =
        (decide (0 < floatReal a) && decide (xr < cr + floatReal a))
      rw [decide_eq_decide.mpr hs, decide_eq_decide.mpr (ht.trans hc0.symm)]
    have htail : ∀ (j : Nat) (hj : j < rest.length),
        xr < (cr + floatReal a) + ((rest.take (j + 1)).map floatReal).sum ↔
          floatReal xf < floatReal ((rest.take (j + 1)).foldl (· + ·) (cf + a)) := by
      intro j hj
      have hh := hc (j + 1) (by simpa using hj)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.foldl_cons] at hh
      simpa only [add_assoc] using hh
    simp only [chooseAux, List.map_cons, htest]
    split
    · rfl
    · exact ih (cf + a) (cr + floatReal a) hf.2.2 htail (index + 1)

/-- An explicit half-ULP accumulation budget and distance from every CDF boundary
suffice to preserve the actual weighted-index result. -/
theorem chooseAux_float_margin (weights : List Binary64) (cf xf : Binary64) (xr η : ℝ)
    (hf : FoldFinite cf weights) (hx : ExecFloat.Binary.isFinite xf = true)
    (he : |floatReal xf - xr| ≤ η)
    (hb : ∀ j : Nat, j < weights.length → foldRoundBudget cf (weights.take (j + 1)) ≤ η)
    (hgap : ∀ j : Nat, j < weights.length →
      2 * η < |xr - (floatReal cf + ((weights.take (j + 1)).map floatReal).sum)|) (index : Nat) :
    chooseAux binary64Arithmetic xf weights cf index =
      chooseAux realArithmetic xr (weights.map floatReal) (floatReal cf) index := by
  apply chooseAux_float_compare_trace weights cf xf (floatReal cf) xr hf hx _ index
  intro j hj
  have hacc := (float_fold_sum_error cf (weights.take (j + 1)) (foldFinite_take cf weights hf _)).trans (hb j hj)
  have hg := hgap j hj
  rw [abs_sub_comm xr (floatReal cf + ((weights.take (j + 1)).map floatReal).sum)] at hg
  have hle := rejection_margin_stable
    (floatReal cf + ((weights.take (j + 1)).map floatReal).sum) xr
    (floatReal ((weights.take (j + 1)).foldl (· + ·) cf)) (floatReal xf) η hacc he
    hg
  simpa only [not_le] using (not_congr hle).symm

end JumpProcessesLean.Proofs
