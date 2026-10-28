/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRCoefficientBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.WitnessBoundEnvelopes

/-! # Gaussian B6 comparison with both Gamma prefix bounds from scale 240 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A positive quadratic root is at least r if its linear term is at least Ar
and its constant term is nonnegative. Compare the square root with the linear term
and clear the positive denominator. This is shared by both Gamma radii. -/
private theorem root_lower {A b z r : ℝ} (hA : 0 < A) (hz : 0 ≤ z) (hb : 2 * A * r ≤ 2 * b) :
    r ≤ (b + Real.sqrt (b ^ 2 + 4 * A * z)) / (2 * A) := by
  have hs :=
    Real.le_sqrt_of_sq_le (show b ^ 2 ≤ b ^ 2 + 4 * A * z by nlinarith only [mul_nonneg hA.le hz])
  exact (le_div_iff₀ (mul_pos (by norm_num only) hA)).mpr (by linarith only [hb, hs])

/-- For nonnegative L and prefix credit C<=28493/5000, the index-100
radius is at least 0.51L. Apply the quadratic-root comparison to its rational
coefficients. The estimate covers both retained prefix credits. -/
private theorem index_radius_lower {L C : ℝ} (hL : 0 ≤ L) (hC : C ≤ 28493 / 5000) :
    (51 / 100 : ℝ) * L ≤ gammaPrefix100Radius L C := by
  apply
    root_lower (by norm_num only : (0 : ℝ) < 91 / 100)
      (by linarith only [hL] : 0 ≤ (7 / 6 : ℝ) * L + 61)
  nlinarith only [hL, hC]

/-- For nonnegative L and prefix credit C<=28493/5000, the clipped
radius is at least 0.51L. Its linear coefficient and nonnegative constant term
allow the same quadratic-root comparison as the index-100 radius. -/
private theorem clipped_radius_lower {L C : ℝ} (hL : 0 ≤ L) (hC : C ≤ 28493 / 5000) :
    (51 / 100 : ℝ) * L ≤ gammaClippedPrefixRoot L C := by
  apply
    root_lower (by norm_num only : (0 : ℝ) < 87069 / 98800)
      (by linarith only [hL] : 0 ≤ (7 / 6 : ℝ) * L + 190 / 3)
  nlinarith only [hL, hC]

/-- For nonnegative L and radius r>=0.51L, the scaled square is at
least 0.63L squared. Square the nonnegative inequality and compare the exact
rational coefficients. This transfers radius bounds to witness bounds. -/
private theorem square_lower {L r : ℝ} (hL : 0 ≤ L) (hr : (51 / 100 : ℝ) * L ≤ r) :
    (63 / 100 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * r ^ 2 := by
  have h0 : 0 ≤ (51 / 100 : ℝ) * L := mul_nonneg (by norm_num only) hL
  have hs := (sq_le_sq₀ h0 (h0.trans hr)).mpr hr
  nlinarith only [hs, sq_nonneg L]

/-- For nonnegative L, the index-100 prefix minimum is at least
0.63L squared. Bound both retained radii and pass through the maxima and minimum.
This lower estimate is used only to compare with B6. -/
private theorem index_lower {L : ℝ} (hL : 0 ≤ L) :
    (63 / 100 : ℝ) * L ^ 2 ≤ gammaIndex100PrefixUpper L := by
  have h1 :=
    square_lower hL (index_radius_lower hL (by norm_num only : (203 / 50 : ℝ) ≤ 28493 / 5000))
  have h2 := square_lower hL (index_radius_lower hL (le_refl (28493 / 5000 : ℝ)))
  exact le_min (h1.trans (le_max_right _ _)) (h2.trans (le_max_right _ _))

/-- For nonnegative L, the clipped Gamma prefix minimum is at least
0.63L squared. Bound the two radii before applying their prefix floors.
This supplies the second Gamma comparison with B6. -/
private theorem clipped_lower {L : ℝ} (hL : 0 ≤ L) :
    (63 / 100 : ℝ) * L ^ 2 ≤ gammaClippedUpper L := by
  have h1 := clipped_radius_lower hL (by norm_num only : (203 / 50 : ℝ) ≤ 28493 / 5000)
  have h2 := clipped_radius_lower hL (le_refl (28493 / 5000 : ℝ))
  have hr1 : (51 / 100 : ℝ) * L ≤ gammaClippedRadius1000 L := by exact h1.trans (le_max_right _ _)
  have hr2 : (51 / 100 : ℝ) * L ≤ gammaClippedPrefixRadius L 50000 (28493 / 5000) :=
    h2.trans (le_max_right _ _)
  exact le_min (square_lower hL hr1) (square_lower hL hr2)

/-- For L>=240, B6 is strictly below the clipped Gamma prefix bound.
Use the B6 upper coefficient and the Gamma lower coefficient. This removes
the clipped candidate from the minimum once B6 applies. -/
theorem gaussianMR6_lt_gammaClipped {L : ℝ} (hL : 240 ≤ L) :
    Analysis.gaussianMR6Bound L < gammaClippedUpper L := by
  exact (Analysis.gaussianMR6Bound_lt_063_sq hL).trans_le (clipped_lower (by linarith only [hL]))

/-- For L>=240, B6 is strictly below the index-100 Gamma prefix bound.
The same separating coefficient works for both prefix credits. This removes
the index-100 candidate from the minimum throughout its applicable range. -/
theorem gaussianMR6_lt_gammaIndex100 {L : ℝ} (hL : 240 ≤ L) :
    Analysis.gaussianMR6Bound L < gammaIndex100PrefixUpper L := by
  exact (Analysis.gaussianMR6Bound_lt_063_sq hL).trans_le (index_lower (by linarith only [hL]))

end PseudoPrime.PrimeTestBounds.MillerRabin
