/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-!
# Elementary alternating-sum bounds

This file bounds alternating sums of nonnegative decreasing real sequences and specializes
them to `1/p^k - 1/x`. It also gives exact alternating sums of affine weights and the rational
inequality `(1 - 1/y)⁻² * (c - b)/2 ≤ c/2 + 13/20` under the stated bounds on `y`, `c`, and `b`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If `y ≥ 8`, `conductorLog ≤ y`, and `1 ≤ piLog ≤ conductorLog`, then multiplying
`(conductorLog - piLog)/2` by `(1 - 1/y)⁻²` gives at most `conductorLog/2 + 13/20`.
Rewriting the inverse factor as `y²/(y - 1)²` and clearing its positive denominator reduces
the estimate to polynomial inequalities. This absorbs the inverse-square loss in conductor bounds.
-/
theorem inverseSquareLogTradeoff {y conductorLog piLog : ℝ} (hy : 8 ≤ y) (hc : conductorLog ≤ y)
    (hp : 1 ≤ piLog) (_hdiff : 0 ≤ conductorLog - piLog) :
    (1 - 1 / y)⁻¹ ^ 2 * ((conductorLog - piLog) / 2) ≤ conductorLog / 2 + 13 / 20 := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 8) hy
  have hyone : 0 < y - 1 := sub_pos.mpr (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 8) hy)
  have hinverse : (1 - 1 / y)⁻¹ ^ 2 = y ^ 2 / (y - 1) ^ 2 := by field_simp [hypos.ne', hyone.ne']
  rw [hinverse, div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hyone)]
  have hfactor : 0 ≤ 2 * y - 1 := by linarith only [hy]
  have hconductorMul := mul_le_mul_of_nonneg_left hc hfactor
  have hpiMul := mul_le_mul_of_nonneg_left hp (sq_nonneg y)
  nlinarith only [hconductorMul, hpiMul, _hdiff, hy, hfactor]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
