/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaExpRationalBounds

/-! # Uniform large-scale ramified dyadic tail bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For every scale at least 40000, the cutoff logarithm divided by sqrt x
is at most 1/16. Apply the logarithm tangent inequality at sqrt x/200.
Certified logarithm bounds and sqrt x>=200 close the estimate uniformly.
This supplies the unbounded tail beyond the finite dyadic scale grid. -/
theorem gamma_dyadic_log_tail_bound {x : ℝ} (hx : 40000 ≤ x) :
    Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x ≤ (1 / 16 : ℝ) := by
  have hx0 : 0 < x := by linarith only [hx]
  have ht : (200 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num only) hx0.le).mpr
      (by
        norm_num only; exact hx)
  have ht0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num only : (0 : ℝ) < 200))
  rw [Real.log_div ht0.ne' (by norm_num only : (200 : ℝ) ≠ 0)] at h
  have he200 : Real.log (200 : ℝ) = Real.log 2 + 2 * Real.log 10 := by
    have he := Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (10 : ℝ) ^ 2 ≠ 0)
    rw [Real.log_pow] at he
    norm_num only [Nat.cast_ofNat] at he
    exact he
  have hl200 : Real.log (200 : ℝ) ≤ 11 / 2 := by
    rw [he200, Real.log_ten_eq]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have he := Real.log_sqrt hx0.le
  have hc : Real.log (99 / 40 : ℝ) ≤ 3 / 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 99 / 40)
    linarith only [hh]
  rw [Real.log_mul (by norm_num only : (99 / 40 : ℝ) ≠ 0) hx0.ne']
  apply (div_le_iff₀ ht0).mpr
  linarith only [h, hl200, he, hc, ht]

/-- At scales at least 40000, the actual weighted ramified dyadic ramp
series is at most 1/16. Bound the cutoff count by its logarithmic quotient
and cancel log two before applying the uniform logarithmic tail bound.
This supplies the actual-series estimate beyond the finite certificate grid. -/
theorem gamma_dyadic_ramified_actual_ramp_tail_le {x : ℝ} (hx : 40000 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (1 / 16 : ℝ) := by
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hr :=
    (gamma_ramp_zero_series_le_count (by norm_num only : 1 < (2 : ℕ)) hx0).trans
      (div_le_div_of_nonneg_right (gamma_ramp_count_le_log (by norm_num only : 1 < (2 : ℕ)) hx1)
        (Real.sqrt_nonneg x))
  have hw := mul_le_mul_of_nonneg_left hr hl0.le
  norm_num only [Nat.cast_ofNat] at hw
  have he :
    Real.log 2 * ((Real.log ((99 / 40 : ℝ) * x) / Real.log 2) / Real.sqrt x) =
      Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
    rw [← mul_div_assoc, mul_comm (Real.log 2) (Real.log ((99 / 40 : ℝ) * x) / Real.log 2),
      div_mul_cancel₀ _ hl0.ne']
  rw [he] at hw
  exact hw.trans (gamma_dyadic_log_tail_bound hx)

end PseudoPrime.Analysis
