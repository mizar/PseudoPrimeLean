/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ComplexExponentialBounds

/-! # Complex powers from rational logarithms -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The exponential is 1-Lipschitz on the closed left half-plane. Factor
the difference at the point with larger real part and use the existing
mean-value estimate for the exponential minus one. -/
private theorem norm_exp_sub_exp_le {z w : ℂ} (hz : z.re ≤ 0) (hw : w.re ≤ 0) :
    ‖Complex.exp z - Complex.exp w‖ ≤ ‖z - w‖ := by
  wlog hzw : z.re ≤ w.re generalizing z w
  · have h := this hw hz (le_of_not_ge hzw)
    simpa only [norm_sub_rev] using h
  have hdiff : (z - w).re ≤ 0 := by
    simp only [Complex.sub_re]
    linarith only [hzw]
  have hnorm : ‖Complex.exp w‖ ≤ 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr hw
  have heq : Complex.exp z - Complex.exp w = Complex.exp w * (Complex.exp (z - w) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, show w + (z - w) = z by ring]
  rw [heq, norm_mul]
  exact
    (mul_le_of_le_one_left (norm_nonneg _) hnorm).trans
      (Analysis.norm_exp_sub_one_le_of_re_nonpos hdiff)

/-- For `Re s ≥ 0` and a positive integer `n`, replacing `log n` by a
nonnegative rational value changes `n⁻ˢ` by at most the logarithm error
times `‖s‖`. This supplies the analytic error for rational term evaluation. -/
theorem norm_cpow_log_approx (s : ℂ) (hs : 0 ≤ s.re) (n : ℕ) (hn : 1 ≤ n) (q : ℚ) (hq : 0 ≤ q)
    {ε : ℝ} (he : |Real.log n - (q : ℝ)| ≤ ε) :
    ‖(n : ℂ) ^ (-s) - Complex.exp ((-s) * (q : ℂ))‖ ≤ ‖s‖ * ε := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num only) hn1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hqR : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hz : ((-s) * (Real.log n : ℂ)).re ≤ 0 := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hlog
  have hw : ((-s) * (q : ℂ)).re ≤ 0 := by
    rw [← Complex.ofReal_ratCast]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hqR
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by exact_mod_cast rfl,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn0.ne'), ← Complex.ofReal_log hn0.le,
    mul_comm]
  have h := norm_exp_sub_exp_le hz hw
  have heq :
    (-s) * (Real.log n : ℂ) - (-s) * (q : ℂ) = (-s) * ((Real.log n - (q : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_ratCast]
    ring
  rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left he (norm_nonneg s))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
