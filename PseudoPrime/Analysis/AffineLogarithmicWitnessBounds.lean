/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.AffineLogarithmicTailBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaWitnessBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaMaximumBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaNonOneProfileBounds

/-! # Analytic tails of squared affine-logarithmic quadratic witness fits -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The logarithm of 10000 is at most ten. Compare with 16384 = 2^14
and use the upper bound on log two. This supplies the initial logarithmic
estimate for the four quadratic fitting-root continuation certificates. -/
theorem qFit_log_ten_thousand_le_ten : Real.log (10000 : ℝ) ≤ 10 := by
  have h :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 10000) (by norm_num only : (10000 : ℝ) ≤ 16384)
  rw [show (16384 : ℝ) = 2 ^ 14 by norm_num only, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

/-- With rational a ≥ 1789/2000, the continuation guards at L = 10000
make the fitting square dominate (4/5)L² for every L ≥ 10000.
The rational comparison slope has square above 4/5, so no irrational coefficient is needed. -/
theorem quadratic_gamma_square_le_affine_root {L : ℝ} {a b c : ℚ} (ha : 1789 / 2000 ≤ a)
    (hL : 10000 ≤ L) (hb : -((a - 1789 / 2000 : ℚ) : ℝ) * 10000 ≤ (b : ℝ))
    (hbase : (1789 / 2000 : ℝ) * 10000 ≤ affineLogarithmicRoot 10000 a b c) :
    (4 / 5 : ℝ) * L ^ 2 ≤ affineLogarithmicRoot L a b c ^ 2 := by
  have hs :=
    affineLogarithmicSquare_ge_linear_square_on_tail (r := 1789 / 2000) (by norm_num only) ha
      (by norm_num only : (0 : ℝ) < 10000) hL hb
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hbase)
  have hc : (4 / 5 : ℝ) ≤ ((1789 / 2000 : ℚ) : ℝ) ^ 2 := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg L)).trans hs

/-- At L = 10000, this quadratic fitting root dominates (1789/2000)L.
The negative log coefficient permits use of the upper logarithm bound.
This verifies the initial guard for its analytic upper interval. -/
theorem qFit_negNineTenths_at_ten_thousand :
    (1789 / 2000 : ℝ) * 10000 ≤
      affineLogarithmicRoot 10000 (9 / 10) (-166161 / 50000) (6168143 / 1000000) := by
  have h := qFit_log_ten_thousand_le_ten
  norm_num only [affineLogarithmicRoot, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  linarith only [h]

/-- For L ≥ 10000, this fitted square dominates the established Gamma bound.
Apply the rational-slope continuation criterion with its verified initial guard.
This is the numerical transfer used by the corresponding actual witness theorem. -/
theorem gamma_square_le_qFit_negNineTenths {L : ℝ} (hL : 10000 ≤ L) :
    (4 / 5 : ℝ) * L ^ 2 ≤
      affineLogarithmicRoot L (9 / 10) (-166161 / 50000) (6168143 / 1000000) ^ 2 := by
  exact
    quadratic_gamma_square_le_affine_root (by norm_num only) hL
      (by norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg])
      qFit_negNineTenths_at_ten_thousand

/-- At L = 10000, this quadratic fitting root dominates (1789/2000)L.
The negative log coefficient permits use of the upper logarithm bound.
This verifies the initial guard for its analytic upper interval. -/
theorem qFit_negOne_at_ten_thousand :
    (1789 / 2000 : ℝ) * 10000 ≤
      affineLogarithmicRoot 10000 1 (-991489 / 250000) (6720131 / 1000000) := by
  have h := qFit_log_ten_thousand_le_ten
  norm_num only [affineLogarithmicRoot, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  linarith only [h]

/-- For L ≥ 10000, this fitted square dominates the established Gamma bound.
Apply the rational-slope continuation criterion with its verified initial guard.
This is the numerical transfer used by the corresponding actual witness theorem. -/
theorem gamma_square_le_qFit_negOne {L : ℝ} (hL : 10000 ≤ L) :
    (4 / 5 : ℝ) * L ^ 2 ≤ affineLogarithmicRoot L 1 (-991489 / 250000) (6720131 / 1000000) ^ 2 := by
  exact
    quadratic_gamma_square_le_affine_root (by norm_num only) hL
      (by norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg])
      qFit_negOne_at_ten_thousand

/-- At L = 10000, this quadratic fitting root dominates (1789/2000)L.
The negative log coefficient permits use of the upper logarithm bound.
This verifies the initial guard for its analytic upper interval. -/
theorem qFit_nonOneNineTenths_at_ten_thousand :
    (1789 / 2000 : ℝ) * 10000 ≤
      affineLogarithmicRoot 10000 (9 / 10) (-1439941 / 500000) (908039 / 250000) := by
  have h := qFit_log_ten_thousand_le_ten
  norm_num only [affineLogarithmicRoot, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  linarith only [h]

/-- For L ≥ 10000, this fitted square dominates the established Gamma bound.
Apply the rational-slope continuation criterion with its verified initial guard.
This is the numerical transfer used by the corresponding actual witness theorem. -/
theorem gamma_square_le_qFit_nonOneNineTenths {L : ℝ} (hL : 10000 ≤ L) :
    (4 / 5 : ℝ) * L ^ 2 ≤
      affineLogarithmicRoot L (9 / 10) (-1439941 / 500000) (908039 / 250000) ^ 2 := by
  exact
    quadratic_gamma_square_le_affine_root (by norm_num only) hL
      (by norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg])
      qFit_nonOneNineTenths_at_ten_thousand

/-- At L = 10000, this quadratic fitting root dominates (1789/2000)L.
The negative log coefficient permits use of the upper logarithm bound.
This verifies the initial guard for its analytic upper interval. -/
theorem qFit_nonOneOne_at_ten_thousand :
    (1789 / 2000 : ℝ) * 10000 ≤
      affineLogarithmicRoot 10000 1 (-1720413 / 500000) (1005597 / 250000) := by
  have h := qFit_log_ten_thousand_le_ten
  norm_num only [affineLogarithmicRoot, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  linarith only [h]

/-- For L ≥ 10000, this fitted square dominates the established Gamma bound.
Apply the rational-slope continuation criterion with its verified initial guard.
This is the numerical transfer used by the corresponding actual witness theorem. -/
theorem gamma_square_le_qFit_nonOneOne {L : ℝ} (hL : 10000 ≤ L) :
    (4 / 5 : ℝ) * L ^ 2 ≤ affineLogarithmicRoot L 1 (-1720413 / 500000) (1005597 / 250000) ^ 2 := by
  exact
    quadratic_gamma_square_le_affine_root (by norm_num only) hL
      (by norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg])
      qFit_nonOneOne_at_ten_thousand

end PseudoPrime.Analysis
