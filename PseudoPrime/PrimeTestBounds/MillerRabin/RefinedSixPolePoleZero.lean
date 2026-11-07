/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCutoffComparison

/-! Vanishing pole residue for the refined sixth-pole kernel. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The refined kernel has no residue at the regularization point minus one half. -/
theorem refined_pole_residue_zero (F : ℂ → ℂ) (x : ℝ) :
    LLS.PaperStatements.MellinKernel.weightedResidue refinedSixPoleKernel F x (-1 / 2) = 0 := by
  simp only [LLS.PaperStatements.MellinKernel.weightedResidue]
  change
    -logDeriv F (-1 / 2) *
        (((-1 / 2 : ℂ) + 1 / 2) * refinedSixPoleKernel.function (-1 / 2) * (x : ℂ) ^ (-1 / 2)) =
      0
  rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]

/-- The refined contour remainder consists exactly of its two vertical integrals. -/
theorem refined_contour_no_residue {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    refinedContourRemainder χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              (refinedSixPoleKernel.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  simp only [refinedContourRemainder, refined_pole_residue_zero, zero_add]

end PseudoPrime.PrimeTestBounds.MillerRabin
