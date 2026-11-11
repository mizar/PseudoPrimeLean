/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevFiveTerm
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositeMangoldtSqrtBound

/-! # Unconditional lower bounds for Chebyshev theta

Separate the elementary five-term main term from the higher-prime-power cost.
These estimates can supply prime logarithmic mass without RH or a prime table.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For `x ≥ 30`, subtract the unconditional higher-prime-power cost from
the five-term lower bound for `psi`. This retains the exact Chebyshev slope. -/
theorem theta_lower_fiveTerm {x : ℝ} (hx : 30 ≤ x) :
    chebyshevSlope * x - 5 * Real.log x + 5 - 6 * Real.sqrt x ≤ Chebyshev.theta x := by
  have hp := psi_lower_fiveTerm hx
  have hd := psi_sub_theta_le_six_sqrt (show 1 ≤ x by linarith only [hx])
  linarith only [hp, hd]

/-- For `x ≥ 4096`, Chebyshev theta is at least `4x/5` unconditionally.
Use a logarithm tangent at 4096 and `sqrt x ≤ x/64` to absorb the errors.
This supplies a linear prime-mass lower bound without finite enumeration. -/
theorem theta_lower_four_fifths {x : ℝ} (hx : 4096 ≤ x) :
    (4 / 5 : ℝ) * x ≤ Chebyshev.theta x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hs : (64 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith only [hx])
  have hsq := Real.sq_sqrt hx0.le
  have hroot : Real.sqrt x ≤ x / 64 := by
    have hm := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg x)
    nlinarith only [hsq, hm]
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos hx0 (by norm_num only : (0 : ℝ) < 4096))
  rw [Real.log_div hx0.ne' (by norm_num only : (4096 : ℝ) ≠ 0),
    show (4096 : ℝ) = 2 ^ (12 : ℕ) by norm_num only, Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have ha : (91 / 100 : ℝ) ≤ chebyshevSlope := by
    linarith only [chebyshevSlope_bounds.1]
  have ham := mul_le_mul_of_nonneg_right ha hx0.le
  have hlog2 : Real.log 2 ≤ (7 / 10 : ℝ) := by linarith only [Real.log_two_lt_d9]
  have ht := theta_lower_fiveTerm (show 30 ≤ x by linarith only [hx])
  nlinarith only [ht, ham, hroot, hlog, hlog2, hx]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
