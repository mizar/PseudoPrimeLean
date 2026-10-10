/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.NumericalLogBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-! # Explicit logarithmic errors relative to square roots

Antitonicity transfers rational base certificates to all larger cutoffs.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Rational lower and upper bounds for the logarithm of one billion.
Use its ninth-power representation and the tangent bound for the logarithm of ten.
These bounds certify the base for the explicit logarithmic decay estimate. -/
private theorem log_billion_bounds : (4 : ℝ) ≤ Real.log 1000000000 ∧ Real.log 1000000000 ≤ 21 := by
  have h10low := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) (by norm_num only : (3 : ℝ) ≤ 10)
  have h10high :=
    log_le_log_add_sub_div (a := (9 : ℝ)) (y := 10) (by norm_num only) (by norm_num only)
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow] at h10high
  rw [show (1000000000 : ℝ) = 10 ^ 9 by norm_num only, Real.log_pow]
  norm_num only at h10high ⊢
  constructor <;> linarith only [h10low, h10high, Real.log_three_gt_d9, Real.log_three_lt_d9]

/-- Above a positive base whose logarithm is at least four, the squared logarithm
divided by the square root is at most its value at the base. Apply antitonicity
of the logarithm divided by the fourth root, then square the nonnegative ratios.
This transfers explicit logarithmic error bounds from one cutoff to all larger ones. -/
theorem log_square_div_sqrt_le_base {b x : ℝ} (hb : 0 < b) (hlog : 4 ≤ Real.log b) (hx : b ≤ x) :
    (Real.log x) ^ 2 / Real.sqrt x ≤ (Real.log b) ^ 2 / Real.sqrt b := by
  have he : Real.exp ((1 / 4 : ℝ)⁻¹) ≤ b := by
    norm_num only
    exact (Real.le_log_iff_exp_le hb).mp hlog
  have ht :=
    Real.log_div_self_rpow_antitoneOn (by norm_num only : (0 : ℝ) < 1 / 4) he (he.trans hx) hx
  have hx0 := hb.trans_le hx
  have hxlog := hlog.trans (Real.log_le_log hb hx)
  have hn : 0 ≤ Real.log x / x ^ ((1 / 4) : ℝ) :=
    div_nonneg ((by norm_num only : (0 : ℝ) ≤ 4).trans hxlog) (Real.rpow_nonneg hx0.le _)
  have hs := mul_self_le_mul_self hn ht
  have hpow (y : ℝ) (hy : 0 ≤ y) : (y ^ ((1 / 4) : ℝ)) ^ 2 = Real.sqrt y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy, Real.sqrt_eq_rpow]
    norm_num only
  simpa only [← pow_two, div_pow, hpow x hx0.le, hpow b hb.le] using hs

/-- At a real cutoff of at least one billion, seven halves times its logarithm plus
one third of its squared logarithm is at most one hundredth of its square root.
Normalize both errors, transfer to the base by antitonicity, and use rational
logarithm and square-root bounds. This absorbs the coarse coset-bound errors. -/
theorem log_error_le_sqrt_hundredth {x : ℝ} (hx : 1000000000 ≤ x) :
    (7 / 2 : ℝ) * Real.log x + (Real.log x) ^ 2 / 3 ≤ Real.sqrt x / 100 := by
  have hb : (0 : ℝ) < 1000000000 := by norm_num only
  have hx0 := hb.trans_le hx
  have hs : (31600 : ℝ) ≤ Real.sqrt 1000000000 := Real.le_sqrt_of_sq_le (by norm_num only)
  have hbp := Real.sqrt_pos.mpr hb
  have hlog := log_billion_bounds
  have he : Real.exp 2 ≤ (1000000000 : ℝ) :=
    (Real.le_log_iff_exp_le hb).mp ((by norm_num only : (2 : ℝ) ≤ 4).trans hlog.1)
  have ht := Real.log_div_sqrt_antitoneOn he (he.trans hx) hx
  have ht2 := log_square_div_sqrt_le_base hb hlog.1 hx
  have hnum : (Real.log (1000000000 : ℝ)) ^ 2 ≤ 441 := by nlinarith only [hlog.1, hlog.2]
  have h1 : Real.log x / Real.sqrt x ≤ (21 : ℝ) / 31600 :=
    ht.trans
      ((div_le_div_of_nonneg_right hlog.2 hbp.le).trans
        (div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hs))
  have h2 : (Real.log x) ^ 2 / Real.sqrt x ≤ (441 : ℝ) / 31600 :=
    ht2.trans
      ((div_le_div_of_nonneg_right hnum hbp.le).trans
        (div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hs))
  have hr : ((7 / 2 : ℝ) * Real.log x + (Real.log x) ^ 2 / 3) / Real.sqrt x ≤ 1 / 100 := by
    simp only [div_eq_mul_inv] at h1 h2 ⊢
    nlinarith only [h1, h2]
  have hm := mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg x)
  rw [div_mul_cancel₀ _ (Real.sqrt_pos.mpr hx0).ne'] at hm
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hm

end PseudoPrime.Analysis
