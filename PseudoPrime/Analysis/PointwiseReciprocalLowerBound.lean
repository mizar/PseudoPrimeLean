/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.PointwiseReciprocalLowerBound2

/-! # Pointwise reciprocal losses retaining the scale-dependent terms -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a real root y. Output: the rational reciprocal loss 1.57722+0.0462/y-(16033/9000)/y^2.
Role: retain the scale dependence before passing to a uniform reciprocal constant. -/
noncomputable def pointwiseReciprocalLoss (y : ℝ) : ℝ :=
  78861 / 50000 + (231 / 5000) / y - (16033 / 9000) / y ^ 2

/-- Input: a root at least seven. Claim: its pointwise reciprocal loss is at least 3/2.
Proof: bound the negative inverse-square term at seven and retain the positive term.
Role: supply the scalar separation's lower loss requirement. -/
theorem pointwiseReciprocalLoss_ge_three_halves {y : ℝ} (hy : 7 ≤ y) :
    (3 / 2 : ℝ) ≤ pointwiseReciprocalLoss y := by
  have hsq : (49 : ℝ) ≤ y ^ 2 := by nlinarith only [hy]
  have hn : 0 ≤ (231 / 5000 : ℝ) / y := div_nonneg (by norm_num only) (by linarith only [hy])
  have hk :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 16033 / 9000)
      (by norm_num only : (0 : ℝ) < 49) hsq
  dsimp only [pointwiseReciprocalLoss]
  linarith only [hn, hk]

/-- Input: any real root. Claim: its pointwise loss is at most 31551/20000.
Proof: complete the quadratic in its reciprocal explicitly.
Role: compare the adaptive loss with the established uniform theorem. -/
theorem pointwiseReciprocalLoss_le_uniform (y : ℝ) :
    pointwiseReciprocalLoss y ≤ (31551 / 20000 : ℝ) := by
  have h :=
    quadratic_remainder_lower (a := (16033 / 9000 : ℝ)) (b := (231 / 10000 : ℝ)) (u := 1 / y)
      (by norm_num only)
  dsimp only [pointwiseReciprocalLoss]
  rw [show (1 / y) ^ 2 = 1 / y ^ 2 by rw [div_pow, one_pow]] at h
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h]

end PseudoPrime.Analysis
