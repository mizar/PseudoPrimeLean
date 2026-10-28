/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalTheorem11S1Subgroup
public import PseudoPrime.LLS.RationalProfileContracts
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorParitySplitBounds

/-! # Parity-improved rational Part 1 profile from 3000 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L ≥ 8, twice the squared logarithmic ratio is at most 271/250.
Use its monotonicity and the certified logarithm of eight.
This absorbs the exceptional-prime contribution into a rational constant. -/
theorem twice_log_sq_div_le_of_ge_eight {L : ℝ} (hL : 8 ≤ L) :
    2 * Real.log L ^ 2 / L ≤ 271 / 250 := by
  have h := strictAntiOn_logSquareRatio.antitoneOn (le_refl (8 : ℝ)) hL hL
  change Real.log L ^ 2 / L ≤ Real.log (8 : ℝ) ^ 2 / 8 at h
  have h8 : Real.log (8 : ℝ) ≤ 52 / 25 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have h80 : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num only)
  have hs := (sq_le_sq₀ h80 (by norm_num only : (0 : ℝ) ≤ 52 / 25)).mpr h8
  norm_num only at hs
  rw [show 2 * Real.log L ^ 2 / L = 2 * (Real.log L ^ 2 / L) by ring]
  linarith only [h, hs]

/-- For L > 0, log L/L^(3/10) ≤ 1227/1000. Apply a logarithmic tangent
at 1359/500 and the certified exponential lower bound at one.
This controls the small-prime contribution for the split exponent 7/10. -/
theorem log_div_rpow_three_tenths_le {L : ℝ} (hL : 0 < L) :
    Real.log L / L ^ (3 / 10 : ℝ) ≤ 1227 / 1000 := by
  have hu0 := Real.rpow_pos_of_pos hL (3 / 10 : ℝ)
  have ht := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num only : (0 : ℝ) < 1359 / 500))
  rw [Real.log_div hu0.ne' (by norm_num only : (1359 / 500 : ℝ) ≠ 0), Real.log_rpow hL] at ht
  have ha : Real.log (1359 / 500 : ℝ) < 1 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 1359 / 500)).mpr
    exact (by norm_num only : (1359 / 500 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
  rw [div_le_iff₀ hu0]
  linarith only [ht, ha, hu0]

end PseudoPrime.Analysis
