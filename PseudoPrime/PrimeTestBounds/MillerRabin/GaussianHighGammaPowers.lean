/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaContour
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaExpansion
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaPowers

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaExpansion
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaPowers

/-! # Integral-test bounds for the Gaussian gamma coefficients -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational lower and upper endpoints for the H33 coefficient at order
`j + 1`. The alternating forward sign is handled before adding the reflected bound. -/
def highGammaHigherBounds (K : HighGaussianKernel) (j N : ℕ) : ℚ × ℚ :=
  let F := gammaPolePowerBounds (9 / 2 - K.pole) j N
  let R := gammaPolePowerBounds (K.pole + 1 / 2) j N
  let p := (-1 : ℚ) ^ (j + 1)
  (-max (p * F.1) (p * F.2) - R.2, -min (p * F.1) (p * F.2) - R.1)

/-- Both high kernels satisfy the rational enclosures for every positive
derivative order. The integral test controls the infinite remainder uniformly in the order. -/
theorem high_gamma_higher_bounds (K : HighGaussianKernel) (j N : ℕ) :
    ((highGammaHigherBounds K j N).1 : ℝ) ≤ highGammaCoeff K (j + 1) ∧
      highGammaCoeff K (j + 1) ≤ ((highGammaHigherBounds K j N).2 : ℝ) := by
  have hf : 0 < (9 / 2 - K.pole : ℚ) := by cases K <;> norm_num only [HighGaussianKernel.pole]
  have hr : 0 < (K.pole + 1 / 2 : ℚ) := by cases K <;> norm_num only [HighGaussianKernel.pole]
  obtain ⟨hf₀, hf₁⟩ := gamma_pole_power_bounds_cast hf j N
  obtain ⟨hr₀, hr₁⟩ := gamma_pole_power_bounds_cast hr j N
  let p := (-1 : ℝ) ^ (j + 1)
  simp only [highGammaHigherBounds, highGammaCoeff, Rat.cast_sub, Rat.cast_neg, Rat.cast_max,
    Rat.cast_min, Rat.cast_mul, Rat.cast_pow, Rat.cast_one, neg_add, ← sub_eq_add_neg]
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_div,
    Rat.cast_ofNat] at hf₀ hf₁ hr₀ hr₁
  by_cases hp : 0 ≤ p
  · exact
      ⟨sub_le_sub (neg_le_neg ((mul_le_mul_of_nonneg_left hf₁ hp).trans (le_max_right _ _))) hr₁,
        sub_le_sub (neg_le_neg ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left hf₀ hp))) hr₀⟩
  · exact
      ⟨sub_le_sub
          (neg_le_neg ((mul_le_mul_of_nonpos_left hf₀ (le_of_not_ge hp)).trans (le_max_left _ _)))
          hr₁,
        sub_le_sub
          (neg_le_neg ((min_le_right _ _).trans (mul_le_mul_of_nonpos_left hf₁ (le_of_not_ge hp))))
          hr₀⟩

/-- The integer endpoints for a positive-order gamma coefficient of a high kernel. -/
def highGammaHigherGrid (K : HighGaussianKernel) (j N D : ℕ) : ℤ × ℤ :=
  gammaHigherGrid K.pole j N D

/-- The shared grid enclosure bounds the high kernel's positive-order coefficient. -/
theorem high_gamma_higher_grid (K : HighGaussianKernel) (j N D : ℕ) (hD : 0 < D) :
    (↑(highGammaHigherGrid K j N D).1 : ℝ) / D ≤ highGammaCoeff K (j + 1) ∧
      highGammaCoeff K (j + 1) ≤ (↑(highGammaHigherGrid K j N D).2 : ℝ) / D := by
  have ha : -(1 / 2) < K.pole := by cases K <;> norm_num only [HighGaussianKernel.pole]
  have ha' : K.pole < 9 / 2 := by cases K <;> norm_num only [HighGaussianKernel.pole]
  simpa only [highGammaHigherGrid, gammaHigherCoeff, highGammaCoeff, Rat.cast_sub, Rat.cast_add,
    Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, neg_add, ← sub_eq_add_neg] using
    gamma_higher_grid ha ha' j N D hD

end PseudoPrime.PrimeTestBounds.MillerRabin
