/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPrimePowers

/-! # Prime-power excess from logarithmic height thirty-six -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `L ≥ 36`, the exponential `exp (L / 6)` is at least `10 * L`.
The bound is used to control prime powers of exponent at least three. -/
theorem exp_sixth_lower36 {L : ℝ} (hL : 36 ≤ L) : 10 * L ≤ Real.exp (L / 6) := by
  have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num only at h ⊢
    linarith only [h]
  have he6 : (400 : ℝ) ≤ Real.exp 6 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2718 / 1000 by norm_num only) he 6
    rw [← Real.exp_nat_mul] at h
    norm_num only at h ⊢
    linarith only [h]
  have ht := Real.add_one_le_exp (L / 6 - 6)
  have hm := mul_le_mul he6 ht (by linarith only [hL]) (Real.exp_pos 6).le
  have heq : Real.exp (L / 6) = Real.exp 6 * Real.exp (L / 6 - 6) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  nlinarith only [hm, hL]

/-- For positive `x` with `log x ≥ 36`, the prime-power excess `ψ x - θ x`
is at most `8/5 * sqrt x`. Combine the prime-square estimate with the
exponential bound for higher powers. -/
theorem psi_sub_theta_36 {x : ℝ} (hx : 0 < x) (hL : 36 ≤ Real.log x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (8 / 5 : ℝ) * Real.sqrt x := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hlog4lt : Real.log 4 < (7 / 5 : ℝ) := by
    rw [hlog4]
    linarith only [Real.log_two_lt_d9]
  have hx4 : 4 ≤ x := by
    by_contra hn
    have hh := Real.log_le_log hx (le_of_not_ge hn)
    linarith only [hh, hlog4lt, hL]
  have hxpow : x ^ (1 / 3 : ℝ) = Real.exp (Real.log x / 3) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hxsqrt : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hexp :
    Real.exp (Real.log x / 2) = Real.exp (Real.log x / 3) * Real.exp (Real.log x / 6) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he := exp_sixth_lower36 hL
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (Real.log x / 3)).le
  have htail : 2 * Real.log x * x ^ (1 / 3 : ℝ) ≤ (1 / 5 : ℝ) * Real.sqrt x := by
    rw [hxpow, hxsqrt, hexp]
    nlinarith only [hm]
  have hfirst := mul_le_mul_of_nonneg_right hlog4lt.le (Real.sqrt_nonneg x)
  have hprime := psi_sub_theta_prime_powers hx4
  linarith only [hprime, hfirst, htail]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
