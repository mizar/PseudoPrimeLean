/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalMellinWeightTail

/-! # Adaptive Taylor orders for rational Mellin weights -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A Taylor order selected from the Gaussian index. The eight cases use
only natural-number comparisons and cover the final Gaussian term as well. -/
def rationalGaussianOrder (k : ℕ) : ℕ :=
  if k = 0 then 71
  else
    if k = 1 then 75
    else
      if k = 2 then 79
      else
        if k = 3 then 87
        else if k = 4 then 95 else if k = 5 then 107 else if k = 6 then 119 else 127

/-- Every selected order is at most the 200th-order analytic truncation. -/
theorem rational_gaussian_order_le (k : ℕ) : rationalGaussianOrder k ≤ 200 := by
  dsimp only [rationalGaussianOrder]
  repeat' split
  all_goals norm_num only

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
-- Each case reduces an exact rational tail majorant; the last uses the common certificate.
/-- For each of the eight Gaussian indices, the common majorant above its
selected order and through order 200 is below `10⁻⁴⁹`. -/
theorem rational_gaussian_adaptive_bound {k : ℕ} (hk : k < 8) :
    rationalGaussianWeightBound 200 k - rationalGaussianWeightBound (rationalGaussianOrder k) k <
      1 / 10 ^ 49 := by
  have hk' : k ≤ 7 := Nat.lt_succ_iff.mp hk
  interval_cases k <;>
    first
    | exact rational_gaussian_tail_bound
    | decide +kernel

/-- For every admissible cell, the rational weight computed to its selected
order differs from the 200th-order weight in one-norm by less than `10⁻⁴⁹`. -/
theorem rational_gaussian_adaptive_tail (t a b p : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) (hp : |p| ≤ 4) {k : ℕ} (hk : k < 8) :
    rationalComplexOneNorm
        (rationalGaussianWeight t a b p 200 k -
          rationalGaussianWeight t a b p (rationalGaussianOrder k) k) <
      1 / 10 ^ 49 := by
  exact
    (rational_gaussian_weight_tail_le t a b p ht ha hab hp (rational_gaussian_order_le k)).trans_lt
      (rational_gaussian_adaptive_bound hk)

end PseudoPrime.Analysis
