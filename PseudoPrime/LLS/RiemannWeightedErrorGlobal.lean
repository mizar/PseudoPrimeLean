/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannChebyshevNumericalBounds
public import PseudoPrime.LLS.RiemannWeightedErrorBounds

/-! # Global square-root error for the logarithmically weighted Mangoldt sum

This extends the existing LLS numerical estimate to nonnegative arguments. No selected
kernel occurs in the contract or imports. The bound can be used for the arithmetic input
of double Abel summation with exponential, gamma, ramp and other integrable weights.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and at every nonnegative argument, the actual logarithmically weighted
Mangoldt sum differs from the argument by at most twice its square root.
Below one the finite sum vanishes; the square-root comparison closes that endpoint case.
This supplies the global arithmetic input for the second Abel integral. -/
theorem mangoldt_log_error_le_two_sqrt (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t| ≤ 2 * Real.sqrt t := by
  by_cases hlarge : 1 < t
  · exact logWeightedMangoldtSum_error_le_two_sqrt hRH hlarge
  · have hsmall := le_of_not_gt hlarge
    rw [logWeightedMangoldtSum_eq_zero_of_le_one hsmall, zero_sub, abs_neg, abs_of_nonneg ht]
    have hsq : t ^ 2 ≤ t := by
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hsmall ht
    have hs : t ≤ Real.sqrt t := (Real.le_sqrt ht ht).mpr hsq
    linarith only [hs, Real.sqrt_nonneg t]

end PseudoPrime.LLS
