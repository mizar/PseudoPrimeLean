/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaLargePrimeCosts

/-! # Positive-coefficient reciprocal bounds for the Gamma Euler cost -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For p>1, the signed full Euler cost is bounded by the positive
coefficient mass divided by p-1. Compare all positive-power series with
the reciprocal geometric series and normalize its denominator. This
controls the large-prime dual excess without discarding a tail error. -/
theorem gamma_prime_euler_cost_le_positive_reciprocal {p : ℝ} (hp : 1 < p) :
    gammaPrimeEulerCost p ≤ (79977719 / 25000000 : ℝ) / (p - 1) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hs :=
    (summable_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)).mul_left
      (79977719 / 25000000 : ℝ)
  have hle :=
    (summable_gammaResolventEulerWeight_powers hp).tsum_le_tsum
      (fun k ↦ by
        simpa only [Real.rpow_neg_one] using
          gamma_euler_weight_le_positive_reciprocal (one_le_pow₀ hp.le : (1 : ℝ) ≤ p ^ (k + 1)))
      hs
  rw [tsum_gammaResolventEulerWeight_powers_eq_cost hp, tsum_mul_left,
    tsum_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)] at hle
  have hr : p ^ (-1 : ℝ) / (1 - p ^ (-1 : ℝ)) = 1 / (p - 1) := by
    have he : 1 - p⁻¹ = p⁻¹ * (p - 1) := by rw [mul_sub, inv_mul_cancel₀ hp0, mul_one]
    rw [Real.rpow_neg_one, he, mul_comm p⁻¹ (p - 1)]
    simpa only [one_mul] using mul_div_mul_right (1 : ℝ) (p - 1) (inv_ne_zero hp0)
  rw [hr] at hle
  simpa only [mul_one_div] using hle

end PseudoPrime.Analysis
