/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalUpperRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerCutoffRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowArithmetic

/-! # Principal upper bounds from the existing prime-power rows -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked Euler row and an aligned upper-weight row bound the principal
summand. The prime-power identity and logarithm endpoint are reused from the
existing Euler certificate rather than checked again. -/
theorem quarter_principal_euler_row_upper {X : ℝ} (hX : 0 < X) (r : EulerCenterRow)
    (hc : eulerCenterRowCheck r = true) (w : QuarterUpperWeightRow) (hw : w.check = true)
    (hi : w.index = r.p ^ (r.k + 1)) (hcut : (w.cut : ℝ) = X) :
    (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X (r.p ^ (r.k + 1))).re ≤
      ((r.hi * ((w.weight : ℚ) / 1000000) : ℚ) : ℝ) := by
  have hp := (eulerCenterRowCheck_sound hc).1
  have hn : r.p ^ (r.k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [refined_principal_summand_eq hX hn, checked_row_mangoldt_eq_log hc]
  have hl := (checked_row_log_bounds hc).2
  have hlog0 : 0 ≤ Real.log r.p := Real.log_natCast_nonneg r.p
  have hw0 : 0 ≤ (w.weight : ℝ) / 1000000 := by positivity
  have hweight := QuarterUpperWeightRow.sound w hw
  rw [hcut, hi] at hweight
  have h := (mul_le_mul_of_nonneg_left hweight hlog0).trans (mul_le_mul_of_nonneg_right hl hw0)
  simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h

/-- Aligned independently certified Euler and weight lists bound their
summed principal contributions by a rational row sum. -/
theorem quarter_principal_euler_rows_upper {X : ℝ} (hX : 0 < X) {rows : List EulerCenterRow}
    {weights : List QuarterUpperWeightRow} (hc : rows.all eulerCenterRowCheck = true)
    (hw : weights.all QuarterUpperWeightRow.check = true)
    (ha : List.Forall₂ (fun r w ↦ w.index = r.p ^ (r.k + 1) ∧ (w.cut : ℝ) = X) rows weights) :
    (rows.map
          (fun r ↦
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X
                (r.p ^ (r.k + 1))).re)).sum ≤
      (((List.zipWith (fun r w ↦ r.hi * ((w.weight : ℚ) / 1000000)) rows weights).sum : ℚ) :
        ℝ) := by
  induction ha with
  | nil => simp only [List.zipWith_nil_left, List.sum_nil, Rat.cast_zero, List.map_nil, le_refl]
  | @cons r w rows weights hrow htail
    ih =>
    have hc' := Bool.and_eq_true_iff.mp hc
    have hw' := Bool.and_eq_true_iff.mp hw
    have h := quarter_principal_euler_row_upper hX r hc'.1 w hw'.1 hrow.1 hrow.2
    simpa only [List.zipWith_cons_cons, List.sum_cons, Rat.cast_add, List.map_cons] using
      add_le_add h (ih hc'.2 hw'.2)

/-- Check that each upper-weight row has the common cutoff and the same
prime-power index as the corresponding existing Euler row. -/
def quarterUpperAlignmentCheck (cut : ℕ) : List EulerCenterRow → List QuarterUpperWeightRow → Bool
  | [], [] => true
  | r :: rows, w :: weights =>
    decide (w.index = r.p ^ (r.k + 1) ∧ w.cut = cut) && quarterUpperAlignmentCheck cut rows weights
  | _, _ => false

/-- A successful alignment check connects each Euler row to its weight row
without rechecking either row's numerical certificate. -/
theorem quarter_upper_alignment_sound {cut : ℕ} {rows : List EulerCenterRow}
    {weights : List QuarterUpperWeightRow}
    (hc : quarterUpperAlignmentCheck cut rows weights = true) :
    List.Forall₂ (fun r w ↦ w.index = r.p ^ (r.k + 1) ∧ (w.cut : ℝ) = (cut : ℝ)) rows weights := by
  induction rows generalizing weights with
  | nil =>
    cases weights with
    | nil => exact List.Forall₂.nil
    | cons w weights => simp only [quarterUpperAlignmentCheck, Bool.false_eq_true] at hc
  | cons r rows ih =>
    cases weights with
    | nil => simp only [quarterUpperAlignmentCheck, Bool.false_eq_true] at hc
    | cons w weights =>
      have h := Bool.and_eq_true_iff.mp hc
      have ha := of_decide_eq_true h.1
      exact List.Forall₂.cons ⟨ha.1, congrArg (fun n : ℕ ↦ (n : ℝ)) ha.2⟩ (ih h.2)

/-- Finite support, exact prime-power rows and aligned upper weights bound
the full principal series. This applies through the existing 50000 cutoff. -/
theorem quarter_principal_euler_prefix_upper {X : ℝ} (hX : 0 < X) {B : ℕ} (hB : B ≤ 50000)
    (hN : ⌊14 * X⌋₊ ≤ B) (weights : List QuarterUpperWeightRow)
    (hw : weights.all QuarterUpperWeightRow.check = true)
    (ha :
      List.Forall₂ (fun r w ↦ w.index = r.p ^ (r.k + 1) ∧ (w.cut : ℝ) = X) (centerRowsBelow B)
        weights) :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re ≤
      (((List.zipWith (fun r w ↦ r.hi * ((w.weight : ℚ) / 1000000)) (centerRowsBelow B)
              weights).sum :
          ℚ) :
        ℝ) := by
  have hsub : Finset.Ioc 0 ⌊14 * X⌋₊ ⊆ Finset.Ioc 0 B := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨hn'.1, hn'.2.trans hN⟩
  have hsum :
    (∑ n ∈ Finset.Ioc 0 ⌊14 * X⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) ≤
      ∑ n ∈ Finset.Ioc 0 B, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ ↦
        LLS.PaperStatements.MellinKernel.principal_summand_re_nonneg refinedSixPoleKernel hX n)
  have hz :
    ∀ n,
      ¬IsPrimePow n → (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re]
    · rw [refined_principal_summand_eq hX hn0, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn,
        zero_mul]
  apply (quarter_principal_support_upper hX).trans (hsum.trans ?_)
  rw [centerRowsBelow_sum _ hz hB]
  exact quarter_principal_euler_rows_upper hX (centerRowsBelow_check B) hw ha

end PseudoPrime.PrimeTestBounds.MillerRabin
