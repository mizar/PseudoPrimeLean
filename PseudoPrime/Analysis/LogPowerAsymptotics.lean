/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Vanishing of logarithmic powers relative to square roots and linear growth. -/

public section

namespace PseudoPrime.Analysis

/-- Every natural power of `log x`, divided by `sqrt x`, tends to zero at infinity.
Specialize the real-power little-o estimate. This controls the arithmetic and square-loss terms. -/
theorem tendsto_log_pow_div_sqrt (n : ℕ) :
    Filter.Tendsto (fun x : ℝ ↦ (Real.log x) ^ n / Real.sqrt x) Filter.atTop (nhds 0) := by
  simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow] using
    (isLittleO_log_rpow_rpow_atTop (n : ℝ)
        (by norm_num only : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero

/-- Every natural power of `log x`, divided by `x`, tends to zero at infinity.
Specialize the real-power little-o estimate. This controls the reciprocal-cutoff terms. -/
theorem tendsto_log_pow_div_self (n : ℕ) :
    Filter.Tendsto (fun x : ℝ ↦ (Real.log x) ^ n / x) Filter.atTop (nhds 0) := by
  simpa only [Real.rpow_natCast, Real.rpow_one] using
    (isLittleO_log_rpow_rpow_atTop (n : ℝ) (by norm_num only : (0 : ℝ) < 1)).tendsto_div_nhds_zero

/-- For positive `c` and `a`, twice the logarithm is eventually bounded by `c * x^a`.
Use the little-o estimate with coefficient `c / 2` and remove the nonnegative norms.
This supplies the exponent comparison for stretched exponential decay. -/
private theorem eventually_two_log_le_mul_rpow {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ x : ℝ in Filter.atTop, 2 * Real.log x ≤ c * x ^ a := by
  have h := (isLittleO_log_rpow_atTop ha).bound (div_pos hc (by norm_num only : (0 : ℝ) < 2))
  filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx1) _)] at hx
  linarith only [hx]

/-- For positive `c` and `a`, `exp (-c * x^a)` is eventually at most `1 / x²`.
Compare exponents using logarithmic little-o, then evaluate the exponential of twice a log.
This converts stretched exponential errors into inverse-square bounds. -/
theorem eventually_exp_neg_rpow_le_inv_sq {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.exp (-c * x ^ a) ≤ 1 / x ^ 2 := by
  filter_upwards [eventually_two_log_le_mul_rpow hc ha, Filter.eventually_ge_atTop (1 : ℝ)] with x
    hx hx1
  calc
    Real.exp (-c * x ^ a) ≤ Real.exp (-(2 * Real.log x)) :=
      Real.exp_le_exp.mpr (by linarith only [hx])
    _ = 1 / x ^ 2 := by
      rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log (zero_lt_one.trans_le hx1), pow_two,
        one_div]

/-- For positive `c` and `a`, `exp (-c * (log x)^a)` is eventually at most `1 / (log x)²`.
Compose the inverse-square stretched exponential bound with the divergence of `log x`.
This reduces quantitative prime-number errors to the second-order logarithmic scale. -/
theorem eventually_exp_neg_log_rpow_le_inv_log_sq {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.exp (-c * (Real.log x) ^ a) ≤ 1 / (Real.log x) ^ 2 := by
  exact Real.tendsto_log_atTop.eventually (eventually_exp_neg_rpow_le_inv_sq hc ha)

/-- Any nonnegative real constant is eventually strictly below a positive
multiple of the squared logarithm on natural inputs. Choose a logarithmic
threshold above the square root of their quotient and square the strict
comparison. This absorbs finite remainder bounds into asymptotic estimates.
The returned threshold is at least two. -/
theorem exists_nat_threshold_const_lt_log_sq {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ q : ℕ, Q ≤ q → B < c * (Real.log q) ^ 2 := by
  have hl :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (Real.sqrt (B / c) + 1)
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp hl
  refine ⟨max 2 Q, le_max_left _ _, ?_⟩
  intro q hq
  have hlog : Real.sqrt (B / c) < Real.log q :=
    lt_of_lt_of_le (lt_add_one _) (hQ q ((le_max_right 2 Q).trans hq))
  have hs := mul_self_lt_mul_self (Real.sqrt_nonneg _) hlog
  have hd : B / c < (Real.log q) ^ 2 := by
    simpa only [← pow_two, Real.sq_sqrt (div_nonneg hB hc.le)] using hs
  exact (div_lt_iff₀ hc).mp hd |>.trans_eq (mul_comm _ _)

end PseudoPrime.Analysis
