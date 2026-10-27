/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannWeightedErrorBounds

/-! # Affine RH error envelopes for the whole exponential half-line -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For x>=1 and u>=0, log(max(1,xu))<=log(x)+u. On the positive-product
branch use log(u)<=u-1; on the other branch the left side is zero.
This yields an affine error envelope valid on the entire half-line. -/
theorem log_max_scaled_le_log_add {x u : ℝ} (hx : 1 ≤ x) (hu : 0 ≤ u) :
    Real.log (max 1 (x * u)) ≤ Real.log x + u := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  by_cases hm : 1 ≤ x * u
  · have hu0 : 0 < u := by
      by_contra h
      have hp := mul_nonpos_of_nonneg_of_nonpos hx0.le (le_of_not_gt h)
      linarith only [hm, hp]
    rw [max_eq_right hm, Real.log_mul hx0.ne' hu0.ne']
    linarith only [Real.log_le_sub_one_of_pos hu0]
  · rw [max_eq_left (le_of_not_ge hm), Real.log_one]
    linarith only [Real.log_nonneg hx, hu]

/-- For u>=0, sqrt(u)<=(u+1)/2. Expand the nonnegative square
(sqrt(u)-1)^2 using sqrt(u)^2=u. This avoids fractional Gamma moments. -/
theorem sqrt_le_half_add_one {u : ℝ} (hu : 0 ≤ u) : Real.sqrt u ≤ (u + 1) / 2 := by
  nlinarith only [Real.sq_sqrt hu, sq_nonneg (Real.sqrt u - 1)]

/-- Under RH, x>=1 and u>=0, the logarithmically weighted error at xu
has the displayed affine envelope. Combine the sharp global error, the clipped
logarithm bound, and the square-root tangent. This controls the whole exponential integral. -/
theorem logWeighted_error_le_exponential_affine (hRH : RiemannHypothesis) {x u : ℝ} (hx : 1 ≤ x)
    (hu : 0 ≤ u) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u| ≤
      Real.sqrt x / 40 * (u + 1) + (1839 / 1000 : ℝ) * (Real.log x + u) + 21 / 20 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  by_cases hu0 : 0 < u
  · have he := logWeightedMangoldtSum_error_le_refined_global hRH (mul_pos hx0 hu0)
    have hl := log_max_scaled_le_log_add hx hu
    have hs :=
      mul_le_mul_of_nonneg_left (sqrt_le_half_add_one hu)
        (div_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 20))
    rw [Real.sqrt_mul hx0.le] at he
    linarith only [he, hl, hs]
  · have heq : u = 0 := le_antisymm (le_of_not_gt hu0) hu
    rw [heq, mul_zero, logWeightedMangoldtSum_eq_zero_of_le_one (by norm_num only), sub_self,
      abs_zero]
    linarith only [Real.sqrt_nonneg x, Real.log_nonneg hx]

/-- Under RH and t>=0, the logarithmically weighted sum is at most 4(t+1).
Specialize the affine error bound at scale one and take its upper side.
This coarse polynomial bound is used only for the decaying endpoint term. -/
theorem logWeightedMangoldtSum_le_four_add_four (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t ≤ 4 * (t + 1) := by
  have he :=
    logWeighted_error_le_exponential_affine hRH (x := 1) (by norm_num only : (1 : ℝ) ≤ 1) ht
  simp only [one_mul, Real.sqrt_one, Real.log_one, zero_add] at he
  have ha := le_abs_self (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t)
  linarith only [he, ha, ht]

end PseudoPrime.LLS
