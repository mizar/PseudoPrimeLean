/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedShiftBounds

/-! # Uniform Gamma numerical budgets from scale 224 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For T ≥ 224, log T ≤ (3/112)T. Anchor the logarithm at 224 and bound
log 250 by six using the logarithms of two and five.
This controls the principal and ramp errors at much smaller scales. -/
theorem gamma_small_scale_log_bound {T : ℝ} (hT : 224 ≤ T) : Real.log T ≤ (3 / 112 : ℝ) * T := by
  have hT0 : 0 < T := by linarith only [hT]
  have h250 : Real.log (250 : ℝ) < 6 := by
    rw [show (250 : ℝ) = 2 * 5 ^ 3 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0)
        (pow_ne_zero 3 (by norm_num only : (5 : ℝ) ≠ 0)),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have h224 :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 224) (by norm_num only : (224 : ℝ) ≤ 250)
  have ht := Real.log_le_sub_one_of_pos (div_pos hT0 (by norm_num only : (0 : ℝ) < 224))
  rw [Real.log_div hT0.ne' (by norm_num only : (224 : ℝ) ≠ 0)] at ht
  linarith only [ht, h224, h250, hT]

/-- For T ≥ 224, the ramp scale exceeds (9/5)^16, the principal normalized
error is at most 3/5 and the ramp normalized error is at most 23.
Combine the logarithmic tangent bound with the rational root lower bound.
These are the common small-scale numerical entrances. -/
theorem gamma_small_scale_bounds {T : ℝ} (hT : 224 ≤ T) :
    let x := (32 / 99 : ℝ) * T ^ 2;
    (9 / 5 : ℝ) ^ 16 ≤ x ∧
      Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10 ≤
        (3 / 5 : ℝ) * Real.sqrt x ∧
      (135 / 20 : ℝ) * Real.sqrt x + 86 * ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20) ≤
        23 * Real.sqrt x := by
  let x := (32 / 99 : ℝ) * T ^ 2
  have hxlarge : (9 / 5 : ℝ) ^ 16 ≤ x := by
    dsimp only [x]
    norm_num only
    nlinarith only [hT, sq_nonneg (T - 224)]
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (9 / 5) ^ 16).trans hxlarge
  have hs := ramp_scale_sqrt_lower (show 0 ≤ T by linarith only [hT])
  have hl := gamma_small_scale_log_bound hT
  have hlogx :=
    Real.log_le_log (zero_lt_one.trans_le hx)
      (show x ≤ T ^ 2 by
        dsimp only [x]; nlinarith only [sq_nonneg T])
  rw [Real.log_pow] at hlogx
  norm_num only [Nat.cast_ofNat] at hlogx
  have hxX : 0 < x * (99 / 40 : ℝ) := mul_pos (zero_lt_one.trans_le hx) (by norm_num only)
  have hlogX :=
    Real.log_le_log hxX
      (show x * (99 / 40 : ℝ) ≤ T ^ 2 by
        dsimp only [x]; nlinarith only [sq_nonneg T])
  rw [Real.log_pow] at hlogX
  norm_num only [Nat.cast_ofNat] at hlogX
  refine ⟨hxlarge, ?_, ?_⟩
  · linarith only [hlogx, hl, hs, hT]
  · linarith only [hlogX, hl, hs, hT]

/-- For T ≥ 224, log T/T^(1/3) ≤ 1. Anchor the cube root at six,
use log six < two and a logarithmic tangent bound.
This controls the factor-support loss on the full small-scale half-line. -/
theorem gamma_small_scale_cuberoot_ratio {T : ℝ} (hT : 224 ≤ T) :
    Real.log T / T ^ (1 / 3 : ℝ) ≤ 1 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hc :=
    Real.rpow_le_rpow (by norm_num only : (0 : ℝ) ≤ 6 ^ 3)
      (show (6 : ℝ) ^ 3 ≤ T by linarith only [hT]) (by norm_num only : (0 : ℝ) ≤ 1 / 3)
  have he : ((6 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 6 := by
    rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 6)]
    norm_num only [Real.rpow_one]
  rw [he] at hc
  have hu0 := Real.rpow_pos_of_pos hT0 (1 / 3 : ℝ)
  have ht := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num only : (0 : ℝ) < 6))
  rw [Real.log_div hu0.ne' (by norm_num only : (6 : ℝ) ≠ 0), Real.log_rpow hT0] at ht
  have h6 : Real.log (6 : ℝ) < 2 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0)]
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  rw [div_le_iff₀ hu0]
  linarith only [hc, ht, h6]

end PseudoPrime.Analysis
