/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalMellinWeight

/-! # Full-order rational Mellin weight certificate -/

public section

namespace PseudoPrime.Analysis

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
-- This exact comparison evaluates the common 200th-order rational majorant.
/-- The common 200th-order error majorant for the eighth Gaussian is below
`10⁻⁴²`. Monotonicity extends this comparison to all eight Gaussian terms. -/
theorem rational_gaussian_error_bound_full :
    rationalGaussianWeightErrorBound 200 7 < 1 / 10 ^ 42 := by decide +kernel

/-- All eight Gaussian terms in every cell of width `1/16` have a
200th-order π-substitution error budget below `10⁻⁴²`, uniformly for
nodes at least one and rational heights of magnitude at most 100. -/
theorem rational_gaussian_error_full_uniform (t a b : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) {k : ℕ} (hk : k < 8) :
    rationalGaussianWeightErrorFast t a b 200 k < 1 / 10 ^ 42 := by
  have hk' : k ≤ 7 := Nat.lt_succ_iff.mp hk
  exact
    lt_of_le_of_lt
      ((rational_gaussian_weight_error_le t a b ht ha hab 200 k).trans
        (rational_gaussian_weight_bound_mono 200 hk'))
      rational_gaussian_error_bound_full

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
-- The 200th-order common norm bound is verified by exact rational reduction.
/-- The common one-norm majorant for the eighth Gaussian and 200th-order
Taylor cells is below two million. -/
theorem rational_gaussian_norm_bound_full : rationalGaussianWeightBound 200 7 < 2000000 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
-- The exact comparison sums the eight individual rational majorants.
/-- The sum of the eight 200th-order weight majorants is below 1700000.
Each summand is calculated from its Gaussian index without a numerical table. -/
theorem rational_gaussian_norm_sum_bound :
    (∑ k ∈ Finset.range 8, rationalGaussianWeightBound 200 k) < 1700000 := by decide +kernel

/-- Every 200th-order rational Gaussian weight in the eight-term range has
one-norm below two million, uniformly over all admissible cells and heights. -/
theorem rational_gaussian_norm_full_uniform (t a b p : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) (hp : |p| ≤ 4) {k : ℕ} (hk : k < 8) :
    rationalComplexOneNorm (rationalGaussianWeight t a b p 200 k) < 2000000 := by
  have hk' : k ≤ 7 := Nat.lt_succ_iff.mp hk
  exact
    lt_of_le_of_lt
      ((rational_gaussian_weight_norm_le t a b p ht ha hab hp 200 k).trans
        (rational_gaussian_weight_norm_bound_mono 200 hk'))
      rational_gaussian_norm_bound_full

/-- The complete 200th-order π-substitution budget for the first grid cell,
height `1413/100` and eighth Gaussian is below `10⁻³⁰`. This follows from
the common certificate and applies the uniform cell-error theorem. -/
theorem rational_gaussian_error_first_full :
    rationalGaussianWeightErrorFast (1413 / 100) 1 (17 / 16) 200 7 < 1 / 10 ^ 30 := by
  have h :=
    rational_gaussian_weight_error_le (1413 / 100) 1 (17 / 16) (by norm_num only) (by norm_num only)
      (by norm_num only) 200 7
  linarith only [h, rational_gaussian_error_bound_full]

end PseudoPrime.Analysis
