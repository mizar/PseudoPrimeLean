/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Below64MainErrorBounds

/-! # Retained even reciprocal error at small analytic scales -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For y>=1, retain the exact even reciprocal error at the square radius.
The nonnegative factor 1-y^(-2) permits the Euler constant lower bound.
This supplies the low-radius endpoint comparison without a uniform error relaxation. -/
theorem evenReciprocalError_le_exact {y : ℝ} (hy : 1 ≤ y) :
    primitiveReciprocalEvenMainError (y ^ 2) ≤
      -(1961 / 2000 : ℝ) + (2 * Real.log y + 103 / 80) / y ^ 2 := by
  have hypos : 0 < y := by linarith only [hy]
  have hxpos : 0 < y ^ 2 := sq_pos_of_pos hypos
  have hfactor : 0 ≤ 1 - 1 / y ^ 2 := by
    apply sub_nonneg.mpr
    apply (div_le_one hxpos).mpr
    nlinarith only [hy]
  have hgammaLower : (23 / 80 : ℝ) ≤ Real.eulerMascheroniConstant / 2 := by
    linarith only [twentyThree_fortieths_lt_eulerMascheroniConstant]
  have hgamma := mul_le_mul_of_nonneg_right hgammaLower hfactor
  have hlog2 : (693 / 1000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  unfold primitiveReciprocalEvenMainError
  rw [Real.log_pow]
  have hneg := neg_le_neg hgamma
  calc
    -Real.log 2 - Real.eulerMascheroniConstant / 2 * (1 - 1 / y ^ 2) +
          (2 * Real.log y + 1) / y ^ 2 ≤
        -(693 / 1000 : ℝ) - (23 / 80 * (1 - 1 / y ^ 2)) + (2 * Real.log y + 1) / y ^ 2 :=
      by nlinarith only [hlog2, hneg]
    _ = -(1961 / 2000 : ℝ) + (2 * Real.log y + 103 / 80) / y ^ 2 := by
      field_simp
      ring

/-- For `y ≥ 8`, the exact even reciprocal main error at `y^2` is bounded by
`-1961/2000 + (2 log y + 103/80)/y^2`. The proof keeps the factor
`1 - y⁻²` attached to the lower bound for `γ/2` before collecting terms. -/
theorem primitiveReciprocalEvenMainError_le_exact_even_envelope {y : ℝ} (hy : 8 ≤ y) :
    primitiveReciprocalEvenMainError (y ^ 2) ≤
      -(1961 / 2000 : ℝ) + (2 * Real.log y + 103 / 80) / y ^ 2 := by
  exact evenReciprocalError_le_exact (by linarith only [hy])

/-- For x at least 64, the even reciprocal main error is at most -179/200.
Use the exact half-ratio identity for the tail, monotonicity of the logarithmic
ratio, and the Euler-constant lower bound 23/40. This retains the improvement
needed by the parity-conditional contour API at finite analytic scales. -/
theorem primitiveReciprocalEvenMainError_le_neg_179_div_200 {x : ℝ} (hx : 64 ≤ x) :
    primitiveReciprocalEvenMainError x ≤ -(179 / 200 : ℝ) := by
  have hxp : 0 < x := by linarith only [hx]
  have hi : 1 / x ≤ (1 / 64 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hx
  have hc : 0 ≤ 1 - 1 / x := by linarith only [hi]
  have hg := mul_le_mul_of_nonneg_right twentyThree_fortieths_lt_eulerMascheroniConstant.le hc
  have hm : logLinearRatio x ≤ logLinearRatio 64 :=
    strictAntiOn_logLinearRatio.antitoneOn (by norm_num only [Set.mem_Ici])
      (by
        simp only [Set.mem_Ici]; linarith only [hx])
      hx
  have h64 : logLinearRatio 64 = (12 * Real.log 2 + 1) / 64 := by
    unfold logLinearRatio
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [h64] at hm
  have he : (Real.log x + 1) / x = logLinearRatio x / 2 + (1 / x) / 2 := by
    unfold logLinearRatio
    ring
  unfold primitiveReciprocalEvenMainError
  rw [he]
  nlinarith only [hi, hg, hm, Real.log_two_gt_d9, Real.log_two_lt_d9]

end PseudoPrime.Analysis
